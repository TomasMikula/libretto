package libretto.typology.toylang.typeinfer

import libretto.lambda.util.Monad
import libretto.lambda.util.Monad.syntax._
import libretto.scaletto.StarterKit._
import libretto.typology.toylang.terms.{Fun, FunT, TypedFun}
import libretto.typology.toylang.types.{AbstractTypeLabel, Type}
import libretto.typology.util.State

object TypeInference {
  type TypeEmitter
  object TypeEmitter {
    def abstractType(v: AbstractTypeLabel): One -⚬ (TypeEmitter |*| Val[Type] |*| TypeEmitter) =
      ???

    def disengage: TypeEmitter -⚬ One =
      ???
  }

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
            val x = unify(x1 |*| x2)
            val h = (f ** x ** g) :>> mapVal { case ((f, x), g) => TypedFun.andThen(f, x, g) }
            a |*| h |*| b
          }
      case FunT.Par(f1, f2) =>
        ???
      case FunT.EitherF(f, g) =>
        ???
      case FunT.InjectL() =>
        ???
      case FunT.InjectR() =>
        ???
      case FunT.FixF(f) =>
        ???
      case FunT.UnfixF(f) =>
        ???
      case FunT.Rec(f) =>
        ???
      case FunT.Recur() =>
        ???
      case FunT.ConstInt(n) =>
        ???
      case FunT.AddInts() =>
        ???
      case FunT.IntToString() =>
        ???
    }

  def unify: (TypeEmitter |*| TypeEmitter) -⚬ Val[Type] =
    ???
}
