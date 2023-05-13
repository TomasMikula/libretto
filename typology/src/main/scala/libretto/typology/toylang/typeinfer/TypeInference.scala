
package libretto.typology.toylang.typeinfer

import libretto.lambda.util.{Monad, SourcePos}
import libretto.lambda.util.Monad.syntax._
import libretto.scaletto.StarterKit._
import libretto.typology.kinds.{●}
import libretto.typology.toylang.terms.{Fun, FunT, TypedFun}
import libretto.typology.toylang.types.{Fix, AbstractTypeLabel, Type, TypeFun, TypeTag}
import libretto.typology.util.State

object TypeInference {
  opaque type TypeEmitter = Rec[TypeEmitterF]
  private type TypeEmitterF[X] = NonAbstractTypeF[X] |+| AbstractTypeF[X]

  private type NonAbstractTypeF[X] = (
    One // unit
    |+| One // int
    |+| One // string
    |+| (Val[TypeFun[●, ●]] |*| X) // apply1
    |+| Val[TypeFun[●, ●]] // fix
    |+| (X |*| X) // recCall
    |+| (X |*| X) // either
    |+| (X |*| X) // pair
  )

  private type NonAbstractType = NonAbstractTypeF[TypeEmitter]

  private type AbstractTypeF[X] = Val[AbstractTypeLabel] |*| RefinementRequestF[X]
  private type RefinementRequestF[X] = -[TypeEmitter.ReboundF[X]]

  private type AbstractType = AbstractTypeF[TypeEmitter]
  private type RefinementRequest = RefinementRequestF[TypeEmitter]

  object TypeEmitter {
    private[TypeInference] type ReboundF[TypeEmitter] = (
      TypeEmitter // refinement
      |+| YieldF[TypeEmitter] // refinement won't come from here
    )

    private type Rebound =
      ReboundF[TypeEmitter]

    private type YieldF[TypeEmitter] = (
      -[TypeEmitter] // refinement came from elsewhere
      |&| One // there won't be any more refinement
    )

    private def pack: TypeEmitterF[TypeEmitter] -⚬ TypeEmitter =
      dsl.pack

    private def unpack: TypeEmitter -⚬ TypeEmitterF[TypeEmitter] =
      dsl.unpack

    def unapply(using SourcePos)(a: $[TypeEmitter])(using LambdaContext): Some[$[TypeEmitterF[TypeEmitter]]] =
      Some(unpack(a))

    def abstractType: (Val[AbstractTypeLabel] |*| -[TypeEmitter.Rebound]) -⚬ TypeEmitter =
      pack ∘ injectR

    def newAbstractType(v: AbstractTypeLabel): One -⚬ (TypeEmitter |*| Val[Type] |*| TypeEmitter) =
      λ.* { _ =>
        producing { case tl |*| t |*| tr =>
          ((abstractType >>: tl) |*| (abstractType >>: tr)) match {
            case (lblL |*| recvL) |*| (lblR |*| recvR) =>
              returning(
                const(v) >>: lblL,
                const(v) >>: lblR,
                t := unifyRebounds(v)(recvL.asInput |*| recvR.asInput),
              )
          }
        }
      }

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

    def string: One -⚬ TypeEmitter =
      pack ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

    def int: One -⚬ TypeEmitter =
      pack ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

    def unify: (TypeEmitter |*| TypeEmitter) -⚬ TypeEmitter =
      λ { case TypeEmitter(a) |*| TypeEmitter(b) =>
        a switch {
          case Right(aLabel |*| aReq) => // `a` is abstract type
            b switch {
              case Right(bLabel |*| bReq) => // `b` is abstract type
                compareLabels(aLabel |*| bLabel) switch {
                  case Left(label) => // labels are same
                    ???
                  case Right(res) =>
                    res switch {
                      case Left(aLabel) =>
                        ???
                      case Right(bLabel) =>
                        ???
                    }
                }
              case Left(b) => // `b` is not abstract type
                refineUnify(aReq |*| b) // TODO: consume aLabel
            }
          case Left(a) => // `a` is not abstract type
            b switch {
              case Right(bLabel |*| bReq) => // `b` is abstract type
                refineUnify(bReq |*| a) // TODO: consume bLabel
              case Left(b) => // `b` is not abstract type
                unifyNonAbstract(a |*| b)
            }
        }
      }

    def refineUnify: (RefinementRequest |*| NonAbstractType) -⚬ TypeEmitter =
      ???

    def unifyNonAbstract: (NonAbstractType |*| NonAbstractType) -⚬ TypeEmitter =
      ???

    def unifyRebounds(v: AbstractTypeLabel): (Rebound |*| Rebound) -⚬ Val[Type] =
      λ { case l |*| r =>
        l switch {
          case Left(refinedL) =>
            r switch {
              case Left(refinedR) =>
                output(unify(refinedL |*| refinedR))
              case Right(unrefinedR) =>
                (refinedL :>> tap) match
                  case refinedL |*| t =>
                    t.alsoElim(refinedL supplyTo chooseL(unrefinedR))
            }
          case Right(unrefinedL) =>
            r switch {
              case Left(refinedR) =>
                (refinedR :>> tap) match
                  case refinedR |*| t =>
                    t.alsoElim(refinedR supplyTo chooseL(unrefinedL))
              case Right(unrefinedR) =>
                constantVal(Type.abstractType(v))
                  .alsoElim(chooseR(unrefinedL))
                  .alsoElim(chooseR(unrefinedR))
            }
        }
      }

    def tap: TypeEmitter -⚬ (TypeEmitter |*| Val[Type]) =
      ???

    def output: TypeEmitter -⚬ Val[Type] = rec { output =>
      unpack > λ { _ switch {
        case Right(label |*| req) => // abstract type
          req.contramap(injectR) switch {
            case Left(--(t)) =>
              output(t)
                .waitFor(neglect(label))
            case Right(no) =>
              (label :>> mapVal { Type.abstractType(_) })
                .alsoElimInv(no)
          }
        case Left(x) =>
          x switch {
            case Right(x1 |*| x2) => // pair
              (output(x1) ** output(x2)) :>> mapVal { case (t1, t2) =>
                Type.pair(t1, t2)
              }
            case Left(x) =>
              x switch {
                case Right(a |*| b) => // either
                  (output(a) ** output(b)) :>> mapVal { case (a, b) =>
                    Type.pair(a, b)
                  }
                case Left(x) =>
                  x switch {
                    case Right(a |*| b) => // recCall
                      (output(a) ** output(b)) :>> mapVal { case (a, b) =>
                        Type.recCall(a, b)
                      }
                    case Left(x) =>
                      x switch {
                        case Right(tf) => // fix
                          tf :>> mapVal { Type.fix(_) }
                        case Left(x) =>
                          x switch {
                            case Right(tf |*| a) => // apply1
                              (tf ** output(a)) :>> mapVal { case (f, a) =>
                                f(a)
                              }
                            case Left(x) =>
                              x switch {
                                case Right(one) => // string
                                  one :>> const(Type.string)
                                case Left(x) =>
                                  x switch {
                                    case Right(one) => // int
                                      one :>> const(Type.int)
                                    case Left(one) => // unit
                                      one :>> const(Type.unit)
                                  }
                              }
                          }
                      }
                  }
              }
          }
      }}
    }

    def disengage: TypeEmitter -⚬ One =
      ???

    private type Label = Val[AbstractTypeLabel]

    private def compareLabels: (Label |*| Label) -⚬ (Label |+| (Label |+| Label)) =
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
          TypeEmitter.newAbstractType(v)
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
            val l1 |*| lt |*| l2 = TypeEmitter.newAbstractType(l)(one)
            val r1 |*| rt |*| r2 = TypeEmitter.newAbstractType(r)(one)
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
            val l1 |*| lt |*| l2 = TypeEmitter.newAbstractType(l)(one)
            val r1 |*| rt |*| r2 = TypeEmitter.newAbstractType(r)(one)
            val f = (lt ** rt) :>> mapVal { case (lt, rt) => TypedFun.injectR[l, r](lt, rt) }
            val b = TypeEmitter.either(l2 |*| r2)
            (r1 |*| f |*| b)
              .alsoElim(TypeEmitter.disengage(l1))
          }
      case FunT.Distribute() =>
        ???
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
            val a1 |*| ta |*| a2 = one :>> TypeEmitter.newAbstractType(va)
            val b1 |*| tb |*| b2 = one :>> TypeEmitter.newAbstractType(vb)
            val tf = (ta ** tb) :>> mapVal { case (ta, tb) => TypedFun.recur[a, b](ta, tb) }
            val tIn = TypeEmitter.pair(TypeEmitter.recCall(a1 |*| b1) |*| a2)
            tIn |*| tf |*| b2
          }
      case FunT.ConstInt(n) =>
        ???
      case FunT.AddInts() =>
        ???
      case FunT.IntToString() =>
        M.pure(
          λ.* { one =>
            val a = one :>> TypeEmitter.int
            val b = one :>> TypeEmitter.string
            val tf = constantVal(TypedFun.intToString)
            a |*| tf |*| b
          }
        )
    }
}
