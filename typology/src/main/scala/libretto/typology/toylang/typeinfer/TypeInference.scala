
package libretto.typology.toylang.typeinfer

import libretto.lambda.util.Monad
import libretto.lambda.util.Monad.syntax._
import libretto.scaletto.StarterKit._
import libretto.typology.kinds.{●}
import libretto.typology.toylang.terms.{Fun, FunT, TypedFun}
import libretto.typology.toylang.types.{Fix, AbstractTypeLabel, Type, TypeFun, TypeTag}
import libretto.typology.util.State

object TypeInference {
  opaque type TypeEmitter = Rec[TypeEmitterF]
  private type TypeEmitterF[X] = (
    One
    |+| (Val[TypeFun[●, ●]] |*| X) // apply1
    |+| Val[TypeFun[●, ●]] // fix
    |+| (X |*| X) // recCall
    |+| (X |*| X) // either
    |+| (X |*| X) // pair
    |+| (Val[AbstractTypeLabel] |*| TypeReceiverF[X])
  )

  private type TypeReceiverF[TypeEmitter] = -[
    TypeEmitter // refinement
    |+| YieldF[TypeEmitter] // refinement won't come from here
  ]

  private type YieldF[TypeEmitter] = -[
    TypeEmitter // refinement came from elsewhere
    |+| One // there won't be any more refinement
  ]

  object TypeEmitter {
    private def pack: TypeEmitterF[TypeEmitter] -⚬ TypeEmitter =
      dsl.pack

    def abstractType(v: AbstractTypeLabel): One -⚬ (TypeEmitter |*| Val[Type] |*| TypeEmitter) =
      ???

    def pair: (TypeEmitter |*| TypeEmitter) -⚬ TypeEmitter =
      pack ∘ injectL ∘ injectR

    def expectPair: TypeEmitter -⚬ (TypeEmitter |*| TypeEmitter) =
      ???

    def either: (TypeEmitter |*| TypeEmitter) -⚬ TypeEmitter =
      pack ∘ injectL ∘ injectL ∘ injectR

    def recCall: (TypeEmitter |*| TypeEmitter) -⚬ TypeEmitter =
      pack ∘ injectL ∘ injectL ∘ injectL ∘ injectR

    def expectRecCall: TypeEmitter -⚬ (TypeEmitter |*| TypeEmitter) =
      ???

    def fix[F[_]](F: TypeTag[F]): One -⚬ TypeEmitter =
      pack ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR ∘ const(TypeTag.toTypeFun(F))

    def apply1[F[_]](F: TypeTag[F]): TypeEmitter -⚬ TypeEmitter =
      λ { x =>
        pack(injectL(injectL(injectL(injectL(injectL(injectR(constantVal(TypeTag.toTypeFun(F)) |*| x)))))))
      }

    def unify: (TypeEmitter |*| TypeEmitter) -⚬ TypeEmitter =
      ???

    def output: TypeEmitter -⚬ Val[Type] =
      ???

    def disengage: TypeEmitter -⚬ One =
      ???
  }

  import TypeEmitter.{output, unify}

  def inferTypes[A, B](f: Fun[A, B]): One -⚬ Val[TypedFun[A, B]] = {
    given VarGen[State[Int, *], AbstractTypeLabel] with {
      override def newVar: State[Int, AbstractTypeLabel] =
        State(n => (n+1, AbstractTypeLabel(n)))
    }

    reconstructTypes[A, B, State[Int, *]](f)
      .map { prg =>
        prg > λ { case a |*| f |*| b =>
          f
            .alsoElim(TypeEmitter.disengage(a))
            .alsoElim(TypeEmitter.disengage(b))
        }
      }
      .run(0)
  }

  def reconstructTypes[A, B, M[_]](f: Fun[A, B])(using
    gen: VarGen[M, AbstractTypeLabel],
    M: Monad[M],
  ): M[One -⚬ (TypeEmitter |*| Val[TypedFun[A, B]] |*| TypeEmitter)] =
    f.value match {
      case FunT.IdFun() =>
        for {
          v <- gen.newVar
        } yield
          TypeEmitter.abstractType(v)
          > λ { case a |*| t |*| b =>
            a |*| (t :>> mapVal(TypedFun.Id(_))) |*| b
          }
      case FunT.AndThen(f, g) =>
        for {
          tf <- reconstructTypes(f)
          tg <- reconstructTypes(g)
        } yield
          λ.* { one =>
            val a |*| f |*| x1 = tf(one)
            val x2 |*| g |*| b = tg(one)
            val x = output(unify(x1 |*| x2))
            val h = (f ** x ** g) :>> mapVal { case ((f, x), g) => TypedFun.andThen(f, x, g) }
            a |*| h |*| b
          }
      case FunT.Par(f1, f2) =>
        for {
          tf1 <- reconstructTypes(f1)
          tf2 <- reconstructTypes(f2)
        } yield
          λ.* { one =>
            val a1 |*| f1 |*| b1 = tf1(one)
            val a2 |*| f2 |*| b2 = tf2(one)
            val a = TypeEmitter.pair(a1 |*| a2)
            val b = TypeEmitter.pair(b1 |*| b2)
            val f = (f1 ** f2) :>> mapVal { case (f1, f2) => TypedFun.par(f1, f2) }
            a |*| f |*| b
          }
      case FunT.EitherF(f, g) =>
        for {
          tf <- reconstructTypes(f)
          tg <- reconstructTypes(g)
        } yield
          λ.* { one =>
            val a1 |*| f |*| b1 = tf(one)
            val a2 |*| g |*| b2 = tg(one)
            val a = TypeEmitter.either(a1 |*| a2)
            val b = unify(b1 |*| b2)
            val h = (f ** g) :>> mapVal { case (f, g) => TypedFun.either(f, g) }
            a |*| h |*| b
          }
      case _: FunT.InjectL[arr, l, r] =>
        for {
          l <- gen.newVar
          r <- gen.newVar
        } yield
          λ.* { one =>
            val l1 |*| lt |*| l2 = TypeEmitter.abstractType(l)(one)
            val r1 |*| rt |*| r2 = TypeEmitter.abstractType(r)(one)
            val f = (lt ** rt) :>> mapVal { case (lt, rt) => TypedFun.injectL[l, r](lt, rt) }
            val b = TypeEmitter.either(l2 |*| r2)
            (l1 |*| f |*| b)
              .alsoElim(TypeEmitter.disengage(r1))
          }
      case _: FunT.InjectR[arr, l, r] =>
        for {
          l <- gen.newVar
          r <- gen.newVar
        } yield
          λ.* { one =>
            val l1 |*| lt |*| l2 = TypeEmitter.abstractType(l)(one)
            val r1 |*| rt |*| r2 = TypeEmitter.abstractType(r)(one)
            val f = (lt ** rt) :>> mapVal { case (lt, rt) => TypedFun.injectR[l, r](lt, rt) }
            val b = TypeEmitter.either(l2 |*| r2)
            (r1 |*| f |*| b)
              .alsoElim(TypeEmitter.disengage(l1))
          }
      case f: FunT.FixF[arr, f] =>
        M.pure(
          λ.* { one =>
            val fixF = TypeEmitter.fix(f.f)(one)
            val fFixF = TypeEmitter.apply1(f.f)(TypeEmitter.fix(f.f)(one))
            val tf = constantVal(TypedFun.fix(f.f))
            fFixF |*| tf |*| fixF
          }
        )
      case f: FunT.UnfixF[arr, f] =>
        M.pure(
          λ.* { one =>
            val fixF = TypeEmitter.fix(f.f)(one)
            val fFixF = TypeEmitter.apply1(f.f)(TypeEmitter.fix(f.f)(one))
            val tf = constantVal(TypedFun.unfix(f.f))
            fixF |*| tf |*| fFixF
          }
        )
      case FunT.Rec(f) =>
        for {
          tf <- reconstructTypes(f)
        } yield
          tf > λ { case aba |*| f |*| b1 =>
            val ab |*| a1 = TypeEmitter.expectPair(aba)
            val a0 |*| b0 = TypeEmitter.expectRecCall(ab)
            val a = unify(a0 |*| a1)
            val b = unify(b0 |*| b1)
            val h = f :>> mapVal { TypedFun.rec(_) }
            a |*| h |*| b
          }
      case _: FunT.Recur[arr, a, b] =>
        for {
          va <- gen.newVar
          vb <- gen.newVar
        } yield
          λ.* { one =>
            val a1 |*| ta |*| a2 = one :>> TypeEmitter.abstractType(va)
            val b1 |*| tb |*| b2 = one :>> TypeEmitter.abstractType(vb)
            val tf = (ta ** tb) :>> mapVal { case (ta, tb) => TypedFun.recur[a, b](ta, tb) }
            val tIn = TypeEmitter.pair(TypeEmitter.recCall(a1 |*| b1) |*| a2)
            tIn |*| tf |*| b2
          }
      case FunT.ConstInt(n) =>
        ???
      case FunT.AddInts() =>
        ???
      case FunT.IntToString() =>
        ???
    }
}
