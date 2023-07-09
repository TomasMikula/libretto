package libretto.typology.toylang.typeinfer

import libretto.lambda.{MonoidalObjectMap, SymmetricMonoidalCategory}
import libretto.lambda.util.{Monad, SourcePos, TypeEq}
import libretto.lambda.util.Monad.syntax._
import libretto.lambda.util.TypeEq.Refl
import libretto.scaletto.StarterKit._
import libretto.scaletto.StarterKit.Comonoid.comonoidOne
import libretto.typology.kinds.{×, ○, ●}
import libretto.typology.toylang.terms.{Fun, FunT, TypedFun}
import libretto.typology.toylang.types.{Fix, AbstractTypeLabel, ScalaTypeParam, TypeAlgebra, TypeFun, TypeTag}
import libretto.typology.util.State

object TypeInference {
  opaque type TypeEmitter[T] = Rec[[X] =>> TypeEmitterF[T, ReboundTypeF[T, X]]]
  opaque type ReboundType[T] = Rec[[X] =>> ReboundTypeF[T, TypeEmitterF[T, X]]]
  private type TypeEmitterF[T, Y] = Rec[TypeSkelet[T, Y, _]]
  private type ReboundTypeF[T, Y] = Rec[TypeSkelet[-[T], Y, _]]

  private type TypeSkelet[T, Y, X] = NonAbstractTypeF[X] |+| AbstractTypeF[T, Y, X]

  private type ConcreteType[T] = Rec[ConcreteTypeF[T, _]]
  private type ConcreteTypeF[T, X] = NonAbstractTypeF[X] |+| TypeParamF[T]

  private type DegenericType = Rec[DegenericTypeF]
  private type DegenericTypeF[X] = NonAbstractTypeF[X] |+| Val[AbstractTypeLabel]

  type Type = TypedFun.Type // libretto.typology.toylang.types.Type[AbstractTypeLabel]
  def  Type = TypedFun.Type // libretto.typology.toylang.types.Type

  type TypeFun[K, L] = libretto.typology.toylang.types.TypeFun[AbstractTypeLabel, K, L]
  // def  TypeFun = libretto.typology.toylang.types.TypeFun

  type TypeTagF = libretto.typology.toylang.types.TypeFun[ScalaTypeParam, ●, ●]

  private type NonAbstractTypeF[X] = (
    Val[(Type, Type)] // type mismatch
    |+| Done // unit
    |+| Done // int
    |+| Done // string
    |+| (Val[TypeTagF] |*| X) // apply1 // TODO: eliminate?
    |+| Val[TypeTagF] // fix
    |+| (X |*| X) // recCall
    |+| (X |*| X) // either
    |+| (X |*| X) // pair
  )

  private type NonAbstractType[T] = NonAbstractTypeF[TypeEmitter[T]]

  /** Type param instantiable to types of "type" T. */
  private type TypeParamF[T] = Val[AbstractTypeLabel] |*| -[T]

  private type AbstractTypeF[T, Y, X] = Val[AbstractTypeLabel] |*| RefinementRequestF[T, Y, X]
  private type RefinementRequestF[T, Y, X] = -[ReboundF[T, Y, X]]

  private type AbstractType[T] = AbstractTypeF[T, ReboundType[T], TypeEmitter[T]]
  private type RefinementRequest[T] = RefinementRequestF[T, ReboundType[T], TypeEmitter[T]]

  private type ReboundF[T, Y, X] = (
    Y // refinement
    |+| YieldF[T, X] // refinement won't come from here
  )

  private type YieldF[T, TypeEmitter] = -[
    TypeEmitter // refinement came from elsewhere
    |+| -[T] // there won't be any more internal refinement, open to a type parameter from the outside
  ] |+| One // disengage (providing no refinement, interested in no further refinement)

  private type Rebound[T] = ReboundF[T, ReboundType[T], TypeEmitter[T]]
  private type Yield[T] = YieldF[T, TypeEmitter[T]]

  object RefinementRequest {
    def map[T, Y, X, Q](g: X -⚬ Q): RefinementRequestF[T, Y, X] -⚬ RefinementRequestF[T, Y, Q] =
      contrapositive(Rebound.contramap(g))

    def contramap[T, Y, X, P](f: P -⚬ Y): RefinementRequestF[T, Y, X] -⚬ RefinementRequestF[T, P, X] =
      contrapositive(Rebound.map(f))

    def completeWith[T, Y, X]: (RefinementRequestF[T, Y, X] |*| Y) -⚬ One =
      λ { case req |*| y => injectL(y) supplyTo req }

    def decline[T, Y, X]: RefinementRequestF[T, Y, X] -⚬ (X |+| -[T]) =
      λ { req =>
        req
          .contramap(injectR ∘ injectL)
          .unInvertWith(forevert > swap)
      }

    def decline0[T, Y, X]: RefinementRequestF[T, Y, X] -⚬ One =
      λ { req =>
        req.contramap(injectR ∘ injectR) :>> unInvertOne
      }

    def merge[T, Y, X](
      splitY: Y -⚬ (Y |*| Y),
    ): (RefinementRequestF[T, Y, X] |*| RefinementRequestF[T, Y, X]) -⚬ RefinementRequestF[T, Y, X] =
      λ { case -(r1) |*| -(r2) =>
        (Rebound.dup(splitY) >>: (r1 |*| r2)).asInputInv
      }

    def mergeFlip[T, Y, X](
      mergeX: (X |*| X) -⚬ X,
      splitX: X -⚬ (X |*| X),
      flipSplitX: X -⚬ (Y |*| Y),
      mergeFlipX: (X |*| X) -⚬ Y,
      newAbstractLink: One -⚬ (X |*| Y),
      instantiate: X -⚬ T,
    ): (RefinementRequestF[T, Y, X] |*| RefinementRequestF[T, Y, X]) -⚬ RefinementRequestF[-[T], X, Y] =
      λ { case -(r1) |*| -(r2) =>
        (Rebound.flopSplit(mergeX, splitX, flipSplitX, mergeFlipX, newAbstractLink, instantiate) >>: (r1 |*| r2)).asInputInv
      }

    def mergeOpWith[P, Q, Y, X](
      splitX: X -⚬ (X |*| X),
      mergeInXY: (X |*| Y) -⚬ X,
      tapFlopYX: Y -⚬ (Y |*| X),
      makeP: Y -⚬ P,
      makeQ: X -⚬ Q,
      tapFlipPQ: P -⚬ (P |*| Q),
    ): (RefinementRequestF[P, Y, X] |*| RefinementRequestF[Q, X, Y]) -⚬ RefinementRequestF[P, Y, X] =
      factorOutInversion > contrapositive(Rebound.tapFlipWith[P, Q, Y, X](splitX, mergeInXY, tapFlopYX, makeP, makeQ, tapFlipPQ))

    def mergeIn[T, Y, X](
      tapFlopY: Y -⚬ (Y |*| X),
      mergeInXY: (X |*| Y) -⚬ X,
      mergeInXT: (X |*| T) -⚬ X,
      yt: Y -⚬ T,
      mergeT: (T |*| T) -⚬ T,
    ): (RefinementRequestF[T, Y, X] |*| RefinementRequestF[-[T], X, Y]) -⚬ RefinementRequestF[T, Y, X] =
      factorOutInversion > contrapositive(Rebound.tapFlip[T, Y, X](tapFlopY, mergeInXY, mergeInXT, yt, mergeT))

    def flopSplit[T, Y, X]: RefinementRequestF[T, Y, X] -⚬ (RefinementRequestF[-[T], X, Y] |*| RefinementRequestF[-[T], X, Y]) =
      ???

    def tapFlop[T, Y, X](
      splitX: X -⚬ (X |*| X),
      mergeInXY: (X |*| Y) -⚬ X,
      tapFlop: Y -⚬ (Y |*| X),
      mergeT: (T |*| T) -⚬ T,
    ): RefinementRequestF[-[T], X, Y] -⚬ (RefinementRequestF[-[T], X, Y] |*| RefinementRequestF[T, Y, X]) =
      contrapositive(Rebound.mergeFlip(splitX, mergeInXY, tapFlop, mergeT)) > distributeInversion

    def split[T, Y, X](
      splitX: X -⚬ (X |*| X),
      mergeY: (Y |*| Y) -⚬ Y,
      tapFlop: Y -⚬ (Y |*| X),
      mergeT: (T |*| T) -⚬ T,
    ): RefinementRequestF[T, Y, X] -⚬ (RefinementRequestF[T, Y, X] |*| RefinementRequestF[T, Y, X]) =
      λ { case -(r) =>
        val r1 |*| r2 = Rebound.merge(splitX, mergeY, tapFlop, mergeT) >>: r
        r1.asInputInv |*| r2.asInputInv
      }
  }

  object Rebound {
    def map[T, Y, X, Q](f: Y -⚬ Q): ReboundF[T, Y, X] -⚬ ReboundF[T, Q, X] =
      |+|.lmap(f)

    def contramap[T, Y, X, P](g: P -⚬ X): ReboundF[T, Y, X] -⚬ ReboundF[T, Y, P] =
      |+|.rmap(Yield.contramap(g))

    def dup[T, X, Y](
      splitY: Y -⚬ (Y |*| Y),
    ): ReboundF[T, Y, X] -⚬ (ReboundF[T, Y, X] |*| ReboundF[T, Y, X]) =
      either(
        splitY > par(injectL, injectL),
        either(
          λ { yld => injectR(injectL(yld)) |*| injectR(injectR($.one)) }, // XXX: arbitrarily propagating to one side
          λ { case +(one) => injectR(injectR(one)) |*| injectR(injectR(one)) },
        )
      )

    def flopSplit[T, Y, X](
      mergeX: (X |*| X) -⚬ X,
      splitX: X -⚬ (X |*| X),
      flipSplitX: X -⚬ (Y |*| Y),
      mergeFlipX: (X |*| X) -⚬ Y,
      newAbstractLink: One -⚬ (X |*| Y),
      instantiate: X -⚬ T,
    ): ReboundF[-[T], X, Y] -⚬ (ReboundF[T, Y, X] |*| ReboundF[T, Y, X]) =
      either(
        flipSplitX > par(injectL, injectL),
        Yield.flopSplit(mergeX, splitX, mergeFlipX, newAbstractLink, instantiate) > par(injectR, injectR),
      )

    def tapFlipWith[P, Q, Y, X](
      splitX: X -⚬ (X |*| X),
      mergeInXY: (X |*| Y) -⚬ X,
      tapFlopYX: Y -⚬ (Y |*| X),
      makeP: Y -⚬ P,
      makeQ: X -⚬ Q,
      tapFlipPQ: P -⚬ (P |*| Q),
    ): ReboundF[P, Y, X] -⚬ (ReboundF[P, Y, X] |*| ReboundF[Q, X, Y]) =
      either(
        tapFlopYX > par(injectL, injectL),
        Yield.tapFlipWith(splitX, mergeInXY, tapFlopYX, makeP, makeQ, tapFlipPQ) > par(injectR, injectR),
      )

    def tapFlip[T, Y, X](
      tapFlopY: Y -⚬ (Y |*| X),
      mergeInXY: (X |*| Y) -⚬ X,
      mergeInXT: (X |*| T) -⚬ X,
      yt: Y -⚬ T,
      mergeT: (T |*| T) -⚬ T,
    ): ReboundF[T, Y, X] -⚬ (ReboundF[T, Y, X] |*| ReboundF[-[T], X, Y]) =
      either(
        tapFlopY > par(injectL, injectL),
        Yield.tapFlip(mergeInXY, mergeInXT, yt, mergeT) > par(injectR, injectR),
      )

    def mergeFlip[T, Y, X](
      splitX: X -⚬ (X |*| X),
      mergeInXY: (X |*| Y) -⚬ X,
      tapFlop: Y -⚬ (Y |*| X),
      mergeT: (T |*| T) -⚬ T,
    ): (ReboundF[-[T], X, Y] |*| ReboundF[T, Y, X]) -⚬ ReboundF[-[T], X, Y] =
      λ { case a |*| b =>
        a switch {
          case Left(refinedA) =>
            b switch {
              case Left(refinedB) =>
                injectL(mergeInXY(refinedA |*| refinedB))
              case Right(yieldB) =>
                yieldB switch {
                  case Left(yieldB) =>
                    val x1 |*| x2 = splitX(refinedA)
                    returning(
                      injectL(x1),
                      injectL(x2) supplyTo yieldB,
                    )
                  case Right(?(_)) =>
                    injectL(refinedA)
                }
            }
          case Right(yieldA) =>
            b switch {
              case Left(refinedB) =>
                yieldA switch {
                  case Left(yieldA) =>
                    val y |*| x = tapFlop(refinedB)
                    returning(
                      injectL(x),
                      injectL(y) supplyTo yieldA,
                    )
                  case Right(?(_)) =>
                    refinedB :>> crashNow(s"TODO: eliminate this path (${summon[SourcePos]})")
                    // injectL(refinedB)
                }
              case Right(yieldB) =>
                injectR((yieldA |*| yieldB) :>> Yield.mergeFlip(tapFlop, mergeT))
            }
        }
      }

    def mergeIn[T, Y, X](
      splitY: Y -⚬ (Y |*| Y),
      mergeInYX: (Y |*| X) -⚬ Y,
      tapFlip: X -⚬ (X |*| Y),
      splitT: T -⚬ (T |*| T),
    ): (ReboundF[T, Y, X] |*| ReboundF[-[T], X, Y]) -⚬ ReboundF[T, Y, X] =
      λ { case a |*| b =>
        a switch {
          case Left(refinedA) =>
            b switch {
              case Left(refinedB) =>
                injectL(mergeInYX(refinedA |*| refinedB))
              case Right(yieldB) =>
                yieldB switch {
                  case Left(yieldB) =>
                    val y1 |*| y2 = splitY(refinedA)
                    returning(
                      injectL(y1),
                      injectL(y2) supplyTo yieldB,
                    )
                  case Right(?(_)) =>
                    injectL(refinedA)
                }
            }
          case Right(yieldA) =>
            b switch {
              case Left(refinedB) =>
                yieldA switch {
                  case Left(yieldA) =>
                    val x |*| y = tapFlip(refinedB)
                    returning(
                      injectL(y),
                      injectL(x) supplyTo yieldA,
                    )
                  case Right(?(_)) =>
                    ???
                    // injectL(refinedB)
                }
              case Right(yieldB) =>
                injectR((yieldA |*| yieldB) :>> Yield.mergeIn(tapFlip, splitT))
            }
        }
      }

    def merge[T, Y, X](
      splitX: X -⚬ (X |*| X),
      mergeY: (Y |*| Y) -⚬ Y,
      tapFlop: Y -⚬ (Y |*| X),
      mergeT: (T |*| T) -⚬ T,
    ): (ReboundF[T, Y, X] |*| ReboundF[T, Y, X]) -⚬ ReboundF[T, Y, X] =
      λ { case a |*| b =>
        a switch {
          case Left(refinedA) =>
            b switch {
              case Left(refinedB) =>
                injectL(mergeY(refinedA |*| refinedB))
              case Right(yieldB) =>
                yieldB switch {
                  case Left(yieldB) =>
                    val y |*| x = tapFlop(refinedA)
                    returning(
                      injectL(y),
                      injectL(x) supplyTo yieldB,
                    )
                  case Right(?(_)) =>
                    injectL(refinedA)
                }
            }
          case Right(yieldA) =>
            b switch {
              case Left(refinedB) =>
                yieldA switch {
                  case Left(yieldA) =>
                    val y |*| x = tapFlop(refinedB)
                    returning(
                      injectL(y),
                      injectL(x) supplyTo yieldA,
                    )
                  case Right(?(_)) =>
                    injectL(refinedB)
                }
              case Right(yieldB) =>
                injectR((yieldA |*| yieldB) :>> Yield.merge(splitX, mergeT))
            }
        }
      }

    def unifyRebounds[T, Y, X](v: AbstractTypeLabel)(
      mergeY: (Y |*| Y) -⚬ Y,
      outputY: Y -⚬ Val[Type],
      mergeT: (T |*| T) -⚬ T,
      outputT: (Val[AbstractTypeLabel] |*| T) -⚬ Val[Type],
      tapFlop: Y -⚬ (Y |*| X),
    ): (ReboundF[T, Y, X] |*| ReboundF[T, Y, X]) -⚬ Val[Type] =
      λ { case l |*| r =>
        l switch {
          case Left(refinedL) =>
            r switch {
              case Left(refinedR) =>
                outputY(mergeY(refinedL |*| refinedR))
              case Right(unrefinedR) =>
                unrefinedR switch {
                  case Left(unrefinedR) =>
                    val y |*| x = tapFlop(refinedL)
                    returning(
                      outputY(y),
                      injectL(x) supplyTo unrefinedR,
                    )
                  case Right(?(_)) =>
                    outputY(refinedL)
                }
            }
          case Right(unrefinedL) =>
            unrefinedL switch {
              case Left(unrefinedL) =>
                r switch {
                  case Left(refinedR) =>
                    val y |*| x = tapFlop(refinedR)
                    returning(
                      outputY(y),
                      injectL(x) supplyTo unrefinedL,
                    )
                  case Right(unrefinedR) =>
                    unrefinedR switch {
                      case Left(unrefinedR) =>
                        val --(t1) = unrefinedL.contramap(injectR)
                        val --(t2) = unrefinedR.contramap(injectR)
                        val t = mergeT(t1 |*| t2)
                        outputT(constantVal(v) |*| t)
                      case Right(?(_)) =>
                        val --(t) = unrefinedL.contramap(injectR)
                        outputT(constantVal(v) |*| t)
                    }
                }
              case Right(?(_)) =>
                r switch {
                  case Left(refinedR) =>
                    outputY(refinedR)
                  case Right(unrefinedR) =>
                    unrefinedR switch {
                      case Left(unrefinedR) =>
                        val --(t) = unrefinedR.contramap(injectR)
                        outputT(constantVal(v) |*| t)
                      case Right(?(_)) =>
                        constantVal(Type.abstractType(Right(v)))
                    }
                }
            }
        }
      }
  }

  object Yield {
    import TypeEmitter.given

    def contramap[T, X, P](g: P -⚬ X): YieldF[T, X] -⚬ YieldF[T, P] =
      |+|.lmap(contrapositive(|+|.lmap(g)))

    def flopSplit[T, Y, X](
      mergeX: (X |*| X) -⚬ X,
      splitX: X -⚬ (X |*| X),
      mergeFlipX: (X |*| X) -⚬ Y,
      newAbstractLink: One -⚬ (X |*| Y),
      instantiate: X -⚬ T,
    ): YieldF[-[T], Y] -⚬ (YieldF[T, X] |*| YieldF[T, X]) =
      val splitLink: X -⚬ (X |*| Y) =
        ???
      λ { _ switch {
        case Left(-(out)) =>
          producing { case in1 |*| in2 =>
            val x1 = (injectL >>: in1).asInput
            val x2 = (injectL >>: in2).asInput

            out :=
              x1 switch {
                case Left(x1) =>
                  x2 switch {
                    case Left(x2) =>
                      injectL(mergeFlipX(x1 |*| x2))
                    case Right(u) =>
                      val x |*| y = constant(newAbstractLink)
                      returning(
                        injectL(y),
                        instantiate(mergeX(x |*| x1)) supplyTo u,
                      )
                  }
                case Right(t) =>
                  x2 switch {
                    case Left(x2) =>
                      val x |*| y = constant(newAbstractLink)
                      returning(
                        injectL(y),
                        instantiate(mergeX(x |*| x2)) supplyTo t,
                      )
                    case Right(u) =>
                      val x |*| y = constant(newAbstractLink)
                      val x1 |*| x2 = splitX(x)
                      returning(
                        injectL(y),
                        instantiate(x1) supplyTo(t),
                        instantiate(x2) supplyTo(u),
                      )
                  }
              }
          }
        case Right(?(_)) =>
          ???
      }}

    def tapFlipWith[P, Q, Y, X](
      splitX: X -⚬ (X |*| X),
      mergeInXY: (X |*| Y) -⚬ X,
      tapFlopYX: Y -⚬ (Y |*| X),
      makeP: Y -⚬ P,
      makeQ: X -⚬ Q,
      tapFlipPQ: P -⚬ (P |*| Q),
    ): YieldF[P, X] -⚬ (YieldF[P, X] |*| YieldF[Q, Y]) =
      // val aux: (T |*| -[T]) -⚬ -[T] =
      //   λ { case t |*| nt =>
      //     val nt1 |*| t1 = constant(forevert[T])
      //     returning(nt1, mergeT(t |*| t1) supplyTo nt)
      //   }

      λ { _ switch {
        case Left(-(out)) =>
          producing { case in1 |*| in2 =>
            val x = (injectL >>: in1).asInput
            val y = (injectL >>: in2).asInput

            out :=
              x switch {
                case Left(x) =>
                  y switch {
                    case Left(y) =>
                      injectL(mergeInXY(x |*| y))
                    case Right(nq) =>
                      val x1 |*| x2 = splitX(x)
                      returning(
                        injectL(x1),
                        makeQ(x2) supplyTo nq,
                      )
                  }
                case Right(np) =>
                  y switch {
                    case Left(y) =>
                      val y1 |*| x = tapFlopYX(y)
                      returning(
                        injectL(x),
                        makeP(y1) supplyTo np,
                      )
                    case Right(nq) =>
                      producing { out =>
                        val out1 = factorOutInversion >>: contrapositive(tapFlipPQ) >>: injectR >>: out
                        out1 := (np |*| nq)
                      }
                  }
              }
          }
        case Right(one) =>
          one :>> crashNow(s"TODO: eliminate this path ${summon[SourcePos]}")
      }}

    def tapFlip[T, Y, X](
      mergeInXY: (X |*| Y) -⚬ X,
      mergeInXT: (X |*| T) -⚬ X,
      yt: Y -⚬ T,
      mergeT: (T |*| T) -⚬ T,
    ): YieldF[T, X] -⚬ (YieldF[T, X] |*| YieldF[-[T], Y]) =
      val aux: (T |*| -[T]) -⚬ -[T] =
        λ { case t |*| nt =>
          val nt1 |*| t1 = constant(forevert[T])
          returning(nt1, mergeT(t |*| t1) supplyTo nt)
        }

      λ { _ switch {
        case Left(-(out)) =>
          producing { case in1 |*| in2 =>
            val x = (injectL >>: in1).asInput
            val y = (injectL >>: in2).asInput

            out :=
              x switch {
                case Left(x) =>
                  y switch {
                    case Left(y) =>
                      injectL(mergeInXY(x |*| y))
                    case Right(--(u)) =>
                      injectL(mergeInXT(x |*| u))
                  }
                case Right(t) =>
                  y switch {
                    case Left(y) =>
                      injectR(aux(yt(y) |*| t))
                    case Right(--(u)) =>
                      injectR(aux(u |*| t))
                  }
              }
          }
        case Right(one) =>
          one :>> crashNow(s"TODO: eliminate this path ${summon[SourcePos]}")
      }}

    def mergeFlip[T, X, Y](
      tapFlop: Y -⚬ (Y |*| X),
      mergeT: (T |*| T) -⚬ T,
    ): (YieldF[-[T], Y] |*| YieldF[T, X]) -⚬ YieldF[-[T], Y] = {
      val ft: -[-[T]] -⚬ (-[-[T]] |*| -[T]) = {
        val f0: (-[T] |*| T) -⚬ -[T] =
          λ { case u |*| t =>
            val u1 |*| u2 = u :>> contrapositive(mergeT) :>> distributeInversion
            returning(u1, t supplyTo u2)
          }
        contrapositive(f0) > distributeInversion
      }

      λ { case a |*| b =>
        a switch {
          case Left(-(a)) =>
            b switch {
              case Left(-(b)) =>
                producing { r =>
                  (a |*| b) :=
                    (injectL >>: r).asInput switch {
                      case Left(y) =>
                        val y1 |*| x = tapFlop(y)
                        injectL(y1) |*| injectL(x)
                      case Right(t) =>
                        val t1 |*| t2 = ft(t)
                        injectR(t1) |*| injectR(t2)
                    }
                }
              case Right(?(_)) =>
                producing { r =>
                  crashNow(s"TODO: eliminate this path ${summon[SourcePos]}") >>: (a |*| r)
                }
            }
          case Right(?(_)) =>
            b :>> crashNow(s"TODO: eliminate this path ${summon[SourcePos]}")
        }
      }
    }

    def mergeIn[T, X, Y](
      tapFlip: X -⚬ (X |*| Y),
      splitT: T -⚬ (T |*| T),
    ): (YieldF[T, X] |*| YieldF[-[T], Y]) -⚬ YieldF[T, X] = {
      val ft: -[T] -⚬ (-[T] |*| -[-[T]]) = {
        val f0: (T |*| -[T]) -⚬ T =
          λ { case t |*| u =>
            val t1 |*| t2 = splitT(t)
            returning(t1, t2 supplyTo u)
          }
        contrapositive(f0) > distributeInversion
      }

      λ { case a |*| b =>
        a switch {
          case Left(-(a)) =>
            b switch {
              case Left(-(b)) =>
                producing { r =>
                  (a |*| b) :=
                    (injectL >>: r).asInput switch {
                      case Left(x) =>
                        val x1 |*| y = tapFlip(x)
                        injectL(x1) |*| injectL(y)
                      case Right(t) =>
                        val t1 |*| t2 = ft(t)
                        injectR(t1) |*| injectR(t2)
                    }
                }
              case Right(?(_)) =>
                ???
            }
          case Right(?(_)) =>
            ???
        }
      }
    }

    def merge[T, X](
      splitX: X -⚬ (X |*| X),
      mergeT: (T |*| T) -⚬ T,
    ): (YieldF[T, X] |*| YieldF[T, X]) -⚬ YieldF[T, X] =
      λ { case a |*| b =>
        a switch {
          case Left(-(a)) =>
            b switch {
              case Left(-(b)) =>
                producing { r =>
                  (a |*| b) :=
                    (injectL >>: r).asInput switch {
                      case Left(x) =>
                        val x1 |*| x2 = splitX(x)
                        injectL(x1) |*| injectL(x2)
                      case Right(t) =>
                        val t1 |*| t2 = t.contramap(mergeT) :>> distributeInversion
                        injectR(t1) |*| injectR(t2)
                    }
                }
              case Right(?(_)) =>
                producing { r =>
                  (r |*| a) := constant(crashNow("unexpected"))
                }
            }
          case Right(?(_)) =>
            b :>> crashNow("TODO: eliminate this case")
        }
      }
  }

  object ReboundTypeF {
    def pack[T, Y]: TypeSkelet[-[T], Y, ReboundTypeF[T, Y]] -⚬ ReboundTypeF[T, Y] =
      dsl.pack

    def unpack[T, Y]: ReboundTypeF[T, Y] -⚬ TypeSkelet[-[T], Y, ReboundTypeF[T, Y]] =
      dsl.unpack

    def contramap[T, Y, P](f: P -⚬ Y): ReboundTypeF[T, Y] -⚬ ReboundTypeF[T, P] =
      rec { self =>
        unpack[T, Y] > TypeSkelet.dimap(f, self) > pack[T, P]
      }
  }

  object ReboundType {
    def pack0[T]: ReboundTypeF[T, TypeEmitterF[T, ReboundType[T]]] -⚬ ReboundType[T] =
      dsl.pack[[X] =>> ReboundTypeF[T, TypeEmitterF[T, X]]]

    def unpack0[T]: ReboundType[T] -⚬ ReboundTypeF[T, TypeEmitterF[T, ReboundType[T]]] =
      dsl.unpack

    def pack1_[T](
      pack1: TypeEmitterF[T, ReboundType[T]] -⚬ TypeEmitter[T],
    ): ReboundTypeF[T, TypeEmitter[T]] -⚬ ReboundType[T] =
      ReboundTypeF.contramap(pack1) > pack0[T]

    private def pack1[T]: ReboundTypeF[T, TypeEmitter[T]] -⚬ ReboundType[T] =
      rec { self =>
        pack1_(TypeEmitter.pack1_(self))
      }

    def unpack1_[T](
      unpack1: TypeEmitter[T] -⚬ TypeEmitterF[T, ReboundType[T]],
    ): ReboundType[T] -⚬ ReboundTypeF[T, TypeEmitter[T]] =
      unpack0[T] > ReboundTypeF.contramap(unpack1)

    private def unpack1[T]: ReboundType[T] -⚬ ReboundTypeF[T, TypeEmitter[T]] =
      rec { self =>
        unpack1_(TypeEmitter.unpack1_(self))
      }

    def unpack[T]: ReboundType[T] -⚬ TypeSkelet[-[T], TypeEmitter[T], ReboundType[T]] =
      λ { t =>
        val t1: $[ReboundTypeF[T, TypeEmitter[T]]] = unpack1(t)
        val t2: $[TypeSkelet[-[T], TypeEmitter[T], ReboundTypeF[T, TypeEmitter[T]]]] = ReboundTypeF.unpack(t1)
        t2 :>> TypeSkelet.map(pack1)
      }

    def pack[T]: TypeSkelet[-[T], TypeEmitter[T], ReboundType[T]] -⚬ ReboundType[T] =
      λ { t =>
        val t1: $[TypeSkelet[-[T], TypeEmitter[T], ReboundTypeF[T, TypeEmitter[T]]]] = t :>> TypeSkelet.map(unpack1)
        val t2: $[ReboundTypeF[T, TypeEmitter[T]]] = ReboundTypeF.pack(t1)
        pack1(t2)
      }

    def split__[T](
      instantiate: ReboundType[T] -⚬ T,
      splitT: T -⚬ (T |*| T),
      mergeInTX: (T |*| TypeEmitter[T]) -⚬ ReboundType[T],
      mergeOutbound: (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ TypeEmitter[T],
      tapFlip: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]),
    ): ReboundType[T] -⚬ (ReboundType[T] |*| ReboundType[T]) =
      rec { self =>
        unpack > TypeSkelet.split(
          self,
          mergeOutbound, //TypeEmitter.merge__(instantiate, splitT, mergeInTX),
          tapFlip, //TypeEmitter.tapFlip(instantiate, splitT, mergeInTX),
          factorOutInversion > contrapositive(splitT),
        ) > par(pack, pack)
      }


    def split_[T](
      instantiate: ReboundType[T] -⚬ T,
      splitT: T -⚬ (T |*| T),
      mergeInTX: (T |*| TypeEmitter[T]) -⚬ ReboundType[T],
      mergeOutbound: (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ TypeEmitter[T],
      tapFlip: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]),
    ): ReboundType[T] -⚬ (ReboundType[T] |*| ReboundType[T]) =
      split__(instantiate, splitT, mergeInTX, mergeOutbound, tapFlip)

    def split[T](
      instantiate: ReboundType[T] -⚬ T,
      splitT: T -⚬ (T |*| T),
      mergeInTX: (T |*| TypeEmitter[T]) -⚬ ReboundType[T],
      neglectT: T -⚬ Done,
      neglectNT: -[T] -⚬ Done,
    ): ReboundType[T] -⚬ (ReboundType[T] |*| ReboundType[T]) = rec { self =>
      val (tapFlip, mergeIn) = rec2 {
        (
          tapFlip: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]),
          mergeIn: (ReboundType[T] |*| TypeEmitter[T]) -⚬ ReboundType[T],
        ) => (
          TypeEmitter.tapFlip_(instantiate, splitT, mergeInTX, self, mergeIn),
          ReboundType.mergeIn__(instantiate, splitT, neglectT, neglectNT, mergeInTX, tapFlip, self),
        )
      }

      split_(
        instantiate,
        splitT,
        mergeInTX,
        TypeEmitter.merge_(instantiate, splitT, neglectNT, mergeInTX, self, mergeIn),
        tapFlip,
      )
    }

    def merge__[T](
      splitOutbound: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| TypeEmitter[T]),
      mergeIntoOutbound: (TypeEmitter[T] |*| ReboundType[T]) -⚬ TypeEmitter[T],
      mergeInT: (TypeEmitter[T] |*| T) -⚬ TypeEmitter[T],
      makeT: ReboundType[T] -⚬ T,
      mergeT: (T |*| T) -⚬ T,
      neglectT: T -⚬ Done,
      neglectNT: -[T] -⚬ Done,
    ): (ReboundType[T] |*| ReboundType[T]) -⚬ ReboundType[T] =
      rec { self =>
        λ { case a |*| b =>
          (unpack(a) |*| unpack(b))
            :>> TypeSkelet.mergeOp(
              splitOutbound,
              mergeIntoOutbound,
              TypeEmitter.pack,
              tapFlop_(self, mergeInT, makeT, mergeT, neglectT, neglectNT),
              self,
              outputApprox(neglectT),
              mergeT,
            )
            :>> pack
        }
      }

    def merge_[T](
      mergeIntoOutbound: (TypeEmitter[T] |*| ReboundType[T]) -⚬ TypeEmitter[T],
      mergeInT: (TypeEmitter[T] |*| T) -⚬ TypeEmitter[T],
      makeT: ReboundType[T] -⚬ T,
      mergeT: (T |*| T) -⚬ T,
      neglectT: T -⚬ Done,
      neglectNT: -[T] -⚬ Done,
    ): (ReboundType[T] |*| ReboundType[T]) -⚬ ReboundType[T] =
      rec { self =>
        merge__(
          TypeEmitter.split_(
            self,
            tapFlop_(self, mergeInT, makeT, mergeT, neglectT, neglectNT),
            mergeT,
          ),
          mergeIntoOutbound,
          mergeInT,
          makeT,
          mergeT,
          neglectT,
          neglectNT,
        )
      }

    def merge[T](
      mergeInT: (TypeEmitter[T] |*| T) -⚬ TypeEmitter[T],
      makeT: ReboundType[T] -⚬ T,
      mergeT: (T |*| T) -⚬ T,
      neglectT: T -⚬ Done,
      neglectNT: -[T] -⚬ Done,
    ): (ReboundType[T] |*| ReboundType[T]) -⚬ ReboundType[T] =
      rec { self =>
        merge_(
          TypeEmitter.mergeIn(mergeInT, makeT, mergeT, neglectT, neglectNT),
          mergeInT,
          makeT,
          mergeT,
          neglectT,
          neglectNT,
        )
      }

    def mergeIn__[T](
      instantiate: ReboundType[T] -⚬ T,
      splitT: T -⚬ (T |*| T),
      neglectT: T -⚬ Done,
      neglectTypeParam: -[T] -⚬ Done,
      mergeInTX: (T |*| TypeEmitter[T]) -⚬ ReboundType[T],
      tapFlip: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]),
      split: ReboundType[T] -⚬ (ReboundType[T] |*| ReboundType[T]),
    ): (ReboundType[T] |*| TypeEmitter[T]) -⚬ ReboundType[T] = rec { self =>
      par(unpack, TypeEmitter.unpack) > TypeSkelet.mergeOpWith[-[T], T, TypeEmitter[T], ReboundType[T]](
        split,
        self,
        tapFlip,
        factorOutInversion > contrapositive(splitT),
        pack,
        TypeEmitter.pack,
        λ { case y |*| nt =>
          val y1 |*| y2 = y :>> split
          returning(y1, instantiate(y2) supplyTo nt)
        },
        λ { case x |*| --(t) =>
          mergeInTX(t |*| x)
        },
        λ { nt =>
          producing { case nt1 |*| tOut =>
            val t = nt1.asInput
            val t1 |*| t2 = splitT(t)
            tOut := returning(t1, t2 supplyTo nt)
          }
        },
        λ { case t |*| nt =>
          val t1 |*| t2 = splitT(t)
          returning(t1, t2 supplyTo nt)
        },
        outputApprox(neglectT),
        TypeEmitter.outputApprox(neglectTypeParam),
      )
    }

    def mergeIn_[T](
      instantiate: ReboundType[T] -⚬ T,
      splitT: T -⚬ (T |*| T),
      neglectT: T -⚬ Done,
      neglectNT: -[T] -⚬ Done,
      mergeInTX: (T |*| TypeEmitter[T]) -⚬ ReboundType[T],
      mergeOutbound: (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ TypeEmitter[T],
      tapFlip: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]),
    ): (ReboundType[T] |*| TypeEmitter[T]) -⚬ ReboundType[T] =
      mergeIn__(
        instantiate,
        splitT,
        neglectT,
        neglectNT,
        mergeInTX,
        tapFlip,
        split__(instantiate, splitT, mergeInTX, mergeOutbound, tapFlip),
      )

    def mergeIn[T](
      instantiate: ReboundType[T] -⚬ T,
      splitT: T -⚬ (T |*| T),
      neglectT: T -⚬ Done,
      neglectNT: -[T] -⚬ Done,
      mergeInTX: (T |*| TypeEmitter[T]) -⚬ ReboundType[T],
      // mergeOutbound: (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ TypeEmitter[T],
      // tapFlip: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]),
    ): (ReboundType[T] |*| TypeEmitter[T]) -⚬ ReboundType[T] = rec { self =>
      val (split, mergeOutbound, tapFlip) =
        rec3 {
          (
            split: ReboundType[T] -⚬ (ReboundType[T] |*| ReboundType[T]),
            mergeOutbound: (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ TypeEmitter[T],
            tapFlip: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]),
          ) => (
            split__(instantiate, splitT, mergeInTX, mergeOutbound, tapFlip),
            TypeEmitter.merge_(instantiate, splitT, neglectNT, mergeInTX, split, self),
            TypeEmitter.tapFlip_(instantiate, splitT, mergeInTX, split, self),
          )
        }

      println("mergeIn 1")
      val res = mergeIn_(
        instantiate,
        splitT,
        neglectT,
        neglectNT,
        mergeInTX,
        mergeOutbound,
        tapFlip,
      )
      println("mergeIn 2")
      res
    }

    def tapFlop_[T](
      merge: (ReboundType[T] |*| ReboundType[T]) -⚬ ReboundType[T],
      mergeInT: (TypeEmitter[T] |*| T) -⚬ TypeEmitter[T],
      makeT: ReboundType[T] -⚬ T,
      mergeT: (T |*| T) -⚬ T,
      neglectT: T -⚬ Done,
      neglectNT: -[T] -⚬ Done,
    ): ReboundType[T] -⚬ (ReboundType[T] |*| TypeEmitter[T]) = rec { self =>
      val splitX: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| TypeEmitter[T]) =
        TypeEmitter.split_(merge, self, mergeT)

      val mergeInXY: (TypeEmitter[T] |*| ReboundType[T]) -⚬ TypeEmitter[T] =
        TypeEmitter.mergeIn_[T](merge, mergeInT, self, makeT, mergeT, neglectT, neglectNT)

      rec { self =>
        unpack > TypeSkelet.tapFlop(splitX, mergeInXY, self, mergeT) > par(pack, TypeEmitter.pack)
      }
    }

    def tapFlop[T](
      mergeInT: (TypeEmitter[T] |*| T) -⚬ TypeEmitter[T],
      makeT: ReboundType[T] -⚬ T,
      mergeT: (T |*| T) -⚬ T,
      neglectT: T -⚬ Done,
      neglectNT: -[T] -⚬ Done,
    ): ReboundType[T] -⚬ (ReboundType[T] |*| TypeEmitter[T]) =
      tapFlop_(
        merge(mergeInT, makeT, mergeT, neglectT, neglectNT),
        mergeInT,
        makeT,
        mergeT,
        neglectT,
        neglectNT,
      )

    def output[T](
      outputT: (Val[AbstractTypeLabel] |*| T) -⚬ Val[Type],
    ): ReboundType[T] -⚬ Val[Type] = {
      val outputT1: (Val[AbstractTypeLabel] |*| -[-[T]]) -⚬ Val[Type] =
        λ { case lbl |*| --(t) => outputT(lbl |*| t) }

      rec { self =>
        unpack > TypeSkelet.output(self, outputT1)
      }
    }

    def close[T](
      closeT: T -⚬ Done,
    ): ReboundType[T] -⚬ Done =
      rec { self =>
        unpack > TypeSkelet.close(self, λ { case --(t) => closeT(t) })
      }

    def outputApprox[T](
      neglectTypeArg: T -⚬ Done,
    ): ReboundType[T] -⚬ Val[Type] =
      rec { self =>
        unpack > TypeSkelet.outputApprox(
          self,
          λ { case --(t) => neglectTypeArg(t) },
        )
      }

    given junctionReboundType[T]: Junction.Positive[ReboundType[T]] with {
      override def awaitPosFst: (Done |*| ReboundType[T]) -⚬ ReboundType[T] =
        rec { self =>
          snd(unpack) > TypeSkelet.awaitPosFst(self) > pack
        }
    }
  }

  object NonAbstractType {
    def pair[X]: (X |*| X) -⚬ NonAbstractTypeF[X] =
      injectR

    def either[X]: (X |*| X) -⚬ NonAbstractTypeF[X] =
      injectL ∘ injectR

    def recCall[X]: (X |*| X) -⚬ NonAbstractTypeF[X] =
      injectL ∘ injectL ∘ injectR

    def fix[X]: Val[TypeTagF] -⚬ NonAbstractTypeF[X] =
      injectL ∘ injectL ∘ injectL ∘ injectR

    def fixT[X, F[_]](F: TypeTag[F]): One -⚬ NonAbstractTypeF[X] =
      fix ∘ const(TypeTag.toTypeFun(F))

    def apply1[X]: (Val[TypeTagF] |*| X) -⚬ NonAbstractTypeF[X] =
      injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

    def apply1T[X, F[_]](F: TypeTag[F]): X -⚬ NonAbstractTypeF[X] =
      λ { x =>
        apply1(constantVal(TypeTag.toTypeFun(F)) |*| x)
      }

    def string[X]: Done -⚬ NonAbstractTypeF[X] =
      injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

    def int[X]: Done -⚬ NonAbstractTypeF[X] =
      injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

    def unit[X]: Done -⚬ NonAbstractTypeF[X] =
      injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

    def mismatch[X]: Val[(Type, Type)] -⚬ NonAbstractTypeF[X] =
      injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL

    def isPair[X]: NonAbstractTypeF[X] -⚬ (NonAbstractTypeF[X] |+| (X |*| X)) =
      λ { t =>
        t switch {
          case Right(r |*| s) => // pair
            injectR(r |*| s)
          case Left(t) =>
            injectL(injectL(t))
        }
      }

    def isRecCall[X]: NonAbstractTypeF[X] -⚬ (NonAbstractTypeF[X] |+| (X |*| X)) =
      λ { t =>
        t switch {
          case Right(r |*| s) => // pair
            injectL(pair(r |*| s))
          case Left(t) =>
            t switch {
              case Right(r |*| s) => // either
                injectL(either(r |*| s))
              case Left(t) =>
                t switch {
                  case Right(r |*| s) => // RecCall
                    injectR(r |*| s)
                  case Left(t) =>
                    injectL(
                      injectL(injectL(injectL(t)))
                    )
                }
            }
        }
      }

    def map[X, Q](g: X -⚬ Q): NonAbstractTypeF[X] -⚬ NonAbstractTypeF[Q] =
      λ { t =>
        t switch {
          case Right(r |*| s) => // pair
            pair(g(r) |*| g(s))
          case Left(t) =>
            t switch {
              case Right(r |*| s) => // either
                either(g(r) |*| g(s))
              case Left(t) =>
                t switch {
                  case Right(r |*| s) => // RecCall
                    recCall(g(r) |*| g(s))
                  case Left(t) =>
                    t switch {
                      case Right(f) => // fix
                        fix(f)
                      case Left(t) =>
                        t switch {
                          case Right(f |*| x) => // apply1
                            apply1(f |*| g(x))
                          case Left(t) =>
                            t switch {
                              case Right(d) => // string
                                string(d)
                              case Left(t) =>
                                t switch {
                                  case Right(d) => // int
                                    int(d)
                                  case Left(t) =>
                                    t switch {
                                      case Right(d) => // unit
                                        unit(d)
                                      case Left(err) =>
                                        mismatch(err)
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
      }

    def splitMap[X, Y, Z](
      f: X -⚬ (Y |*| Z),
    ): NonAbstractTypeF[X] -⚬ (NonAbstractTypeF[Y] |*| NonAbstractTypeF[Z]) =
      λ { t =>
        t switch {
          case Right(r |*| s) => // pair
            val r1 |*| r2 = f(r)
            val s1 |*| s2 = f(s)
            pair(r1 |*| s1) |*| pair(r2 |*| s2)
          case Left(t) =>
            t switch {
              case Right(r |*| s) => // either
                val r1 |*| r2 = f(r)
                val s1 |*| s2 = f(s)
                either(r1 |*| s1) |*| either(r2 |*| s2)
              case Left(t) =>
                t switch {
                  case Right(r |*| s) => // RecCall
                    val r1 |*| r2 = f(r)
                    val s1 |*| s2 = f(s)
                    recCall(r1 |*| s1) |*| recCall(r2 |*| s2)
                  case Left(t) =>
                    t switch {
                      case Right(+(f)) => // fix
                        fix(f) |*| fix(f)
                      case Left(t) =>
                        t switch {
                          case Right(g |*| x) => // apply1
                            val g1 |*| g2 = dsl.dup(g)
                            val x1 |*| x2 = f(x)
                            apply1(g1 |*| x1) |*| apply1(g2 |*| x2)
                          case Left(t) =>
                            t switch {
                              case Right(+(t)) => // string
                                string(t) |*| string(t)
                              case Left(t) =>
                                t switch {
                                  case Right(+(t)) => // int
                                    int(t) |*| int(t)
                                  case Left(t) =>
                                    t switch {
                                      case Right(+(t)) => // unit
                                        unit(t) |*| unit(t)
                                      case Left(err) =>
                                        err :>> dsl.dup :>> par(mismatch, mismatch)
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
      }

    def split[X](
      splitX: X -⚬ (X |*| X),
    ): NonAbstractTypeF[X] -⚬ (NonAbstractTypeF[X] |*| NonAbstractTypeF[X]) =
      splitMap(splitX)

    def flopMerge[Y, X]: NonAbstractTypeF[X] -⚬ (Y |*| NonAbstractTypeF[X]) =
      ???

    def flopSplit[Y, X]: NonAbstractTypeF[X] -⚬ (NonAbstractTypeF[Y] |*| NonAbstractTypeF[Y]) =
      ???

    def mergeWith[X, Y, Z](
      g: (X |*| Y) -⚬ Z,
      outputXApprox: X -⚬ Val[Type],
      outputYApprox: Y -⚬ Val[Type],
    ): (NonAbstractTypeF[X] |*| NonAbstractTypeF[Y]) -⚬ NonAbstractTypeF[Z] = {
      λ { case a |*| b =>
        a switch {
          case Right(a1 |*| a2) => // `a` is a pair
            b switch {
              case Right(b1 |*| b2) => // `b` is a pair
                NonAbstractType.pair(g(a1 |*| b1) |*| g(a2 |*| b2))
              case Left(b) =>
                NonAbstractType.mismatch(
                  ((outputXApprox(a1) ** outputXApprox(a2)) :>> mapVal { case (a1, a2) => Type.pair(a1, a2) })
                  ** output(outputYApprox)(injectL(b))
                )
            }
          case Left(a) =>
            b switch {
              case Right(b1 |*| b2) => // `b` is a pair
                NonAbstractType.mismatch(
                  output(outputXApprox)(injectL(a))
                  ** ((outputYApprox(b1) ** outputYApprox(b2)) :>> mapVal { case (b1, b2) => Type.pair(b1, b2) })
                )
              case Left(b) =>
                a switch {
                  case Right(p |*| q) => // `a` is either
                    b switch {
                      case Right(r |*| s) => // `b` is either
                        NonAbstractType.either(g(p |*| r) |*| g(q |*| s))
                      case Left(b) =>
                        NonAbstractType.mismatch(
                          ((outputXApprox(p) ** outputXApprox(q)) :>> mapVal { case (p, q) => Type.sum(p, q) })
                          ** output(outputYApprox)(injectL(injectL(b)))
                        )
                    }
                  case Left(a) =>
                    b switch {
                      case Right(r |*| s) => // `b` is either
                        NonAbstractType.mismatch(
                          output(outputXApprox)(injectL(injectL(a)))
                          ** ((outputYApprox(r) ** outputYApprox(s)) :>> mapVal { case (r, s) => Type.sum(r, s) })
                        )
                      case Left(b) =>
                        a switch {
                          case Right(p |*| q) => // `a` is RecCall
                            b switch {
                              case Right(r |*| s) => // `b` is RecCall
                                NonAbstractType.recCall(g(p |*| r) |*| g(q |*| s))
                              case Left(b) =>
                                NonAbstractType.mismatch(
                                  ((outputXApprox(p) ** outputXApprox(q)) :>> mapVal { case (p, q) => Type.recCall(p, q) })
                                  ** output(outputYApprox)(injectL(injectL(injectL(b))))
                                )
                            }
                          case Left(a) =>
                            b switch {
                              case Right(r |*| s) => // `b` is RecCall
                                NonAbstractType.mismatch(
                                  output(outputXApprox)(injectL(injectL(injectL(a))))
                                  ** ((outputYApprox(r) ** outputYApprox(s)) :>> mapVal { case (r, s) => Type.recCall(r, s) })
                                )
                              case Left(b) =>
                                a switch {
                                  case Right(f) => // `a` is fix
                                    b switch {
                                      case Right(g) => // `b` is fix
                                        ((f ** g) :>> mapVal { case (f, g) =>
                                          if (f == g) Left(f)
                                          else        Right((f, g))
                                        } :>> liftEither) switch {
                                          case Left(f)   => NonAbstractType.fix(f)
                                          case Right(fg) => NonAbstractType.mismatch(fg :>> mapVal { case (f, g) => (Type.fix(f.vmap(Left(_))), Type.fix(g.vmap(Left(_)))) })
                                        }
                                      case Left(b) =>
                                        NonAbstractType.mismatch(
                                          (f :>> mapVal { f => Type.fix(f.vmap(Left(_))) })
                                          ** output(outputYApprox)(injectL(injectL(injectL(injectL(b)))))
                                        )
                                    }
                                  case Left(a) =>
                                    b switch {
                                      case Right(g) => // `b` is fix
                                        NonAbstractType.mismatch(
                                          output(outputXApprox)(injectL(injectL(injectL(injectL(a)))))
                                          ** (g :>> mapVal { g => Type.fix(g.vmap(Left(_))) })
                                        )
                                      case Left(b) =>
                                        a switch {
                                          case Right(f |*| x) => // `a` is apply1
                                            b switch {
                                              case Right(h |*| y) => // `b` is apply1
                                                ((f ** h) :>> mapVal { case (f, h) =>
                                                  if (f == h) Left(f)
                                                  else        Right((f, h))
                                                } :>> liftEither) switch {
                                                  case Left(f) =>
                                                    NonAbstractType.apply1(f |*| g(x |*| y))
                                                  case Right(fh) =>
                                                    val x1 = outputXApprox(x)
                                                    val y1 = outputYApprox(y)
                                                    // XXX: of course it is wrong to conclude from f != h that f(x) != h(y)
                                                    NonAbstractType.mismatch((fh ** (x1 ** y1)) :>> mapVal { case ((f, h), (x, y)) => (f.vmap(Left(_))(x), h.vmap(Left(_))(y)) })
                                                }
                                              case Left(b) =>
                                                NonAbstractType.mismatch(
                                                  ((f ** outputXApprox(x)) :>> mapVal { case (f, x) => f.vmap(Left(_))(x) })
                                                  ** output(outputYApprox)(injectL(injectL(injectL(injectL(injectL(b)))))),
                                                )
                                            }
                                          case Left(a) =>
                                            b switch {
                                              case Right(g |*| y) => // `b` is apply1
                                                (a |*| g |*| y) :>> crashNow(s"Not implemented (at ${summon[SourcePos]})")
                                              case Left(b) =>
                                                a switch {
                                                  case Right(x) => // `a` is string
                                                    b switch {
                                                      case Right(y) => // `b` is string
                                                        NonAbstractType.string(join(x |*| y))
                                                      case Left(b) =>
                                                        NonAbstractType.mismatch(
                                                          (x :>> constVal(Type.string))
                                                          ** output(outputXApprox)(injectL(injectL(injectL(injectL(injectL(injectL(b)))))))
                                                        )
                                                    }
                                                  case Left(a) =>
                                                    b switch {
                                                      case Right(y) => // `b` is string
                                                        NonAbstractType.mismatch(
                                                          output(outputXApprox)(injectL(injectL(injectL(injectL(injectL(injectL(a)))))))
                                                          ** (y :>> constVal(Type.string))
                                                        )
                                                      case Left(b) =>
                                                        a switch {
                                                          case Right(x) => // `a` is int
                                                            b switch {
                                                              case Right(y) => // `b` is int
                                                                NonAbstractType.int(join(x |*| y))
                                                              case Left(b) =>
                                                                NonAbstractType.mismatch(
                                                                  (x :>> constVal(Type.int))
                                                                  ** output(outputXApprox)(injectL(injectL(injectL(injectL(injectL(injectL(injectL(b))))))))
                                                                )
                                                            }
                                                          case Left(a) =>
                                                            b switch {
                                                              case Right(y) => // `b` is int
                                                                NonAbstractType.mismatch(
                                                                  output(outputXApprox)(injectL(injectL(injectL(injectL(injectL(injectL(injectL(a))))))))
                                                                  ** (y :>> constVal(Type.int))
                                                                )
                                                              case Left(b) =>
                                                                a switch {
                                                                  case Right(x) => // `a` is unit
                                                                    b switch {
                                                                      case Right(y) => // `b` is unit
                                                                        NonAbstractType.unit(join(x |*| y))
                                                                      case Left(bx) => // `b` is type mismatch
                                                                        val tb = bx :>> mapVal { case (t, u) => Type.typeMismatch(t, u) }
                                                                        val ta = x :>> constVal(Type.unit[TypedFun.Label])
                                                                        NonAbstractType.mismatch(ta ** tb)
                                                                    }
                                                                  case Left(ax) => // `a` is type mismatch
                                                                    val ta = ax :>> mapVal { case (t, u) => Type.typeMismatch(t, u) }
                                                                    b switch {
                                                                      case Right(y) => // `b` is unit
                                                                        val tb = y :>> constVal(Type.unit[TypedFun.Label])
                                                                        NonAbstractType.mismatch(ta ** tb)
                                                                      case Left(bx) => // `b` is type mismatch
                                                                        val tb = bx :>> mapVal { case (t, u) => Type.typeMismatch(t, u) }
                                                                        NonAbstractType.mismatch(ta ** tb)
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
      }
    }

    def merge[X](
      mergeX: (X |*| X) -⚬ X,
      outputXApprox: X -⚬ Val[Type],
    ): (NonAbstractTypeF[X] |*| NonAbstractTypeF[X]) -⚬ NonAbstractTypeF[X] =
      mergeWith[X, X, X](mergeX, outputXApprox, outputXApprox)

    def mergeFlip[Y, X](): (NonAbstractTypeF[X] |*| NonAbstractTypeF[X]) -⚬ NonAbstractTypeF[Y] =
      ???

    def output[X](
      outputX: X -⚬ Val[Type],
    ): NonAbstractTypeF[X] -⚬ Val[Type] =
      λ { x =>
        x switch {
          case Right(x1 |*| x2) => // pair
            (outputX(x1) ** outputX(x2)) :>> mapVal { case (t1, t2) =>
              Type.pair(t1, t2)
            }
          case Left(x) =>
            x switch {
              case Right(a |*| b) => // either
                (outputX(a) ** outputX(b)) :>> mapVal { case (a, b) =>
                  Type.pair(a, b)
                }
              case Left(x) =>
                x switch {
                  case Right(a |*| b) => // recCall
                    (outputX(a) ** outputX(b)) :>> mapVal { case (a, b) =>
                      Type.recCall(a, b)
                    }
                  case Left(x) =>
                    x switch {
                      case Right(tf) => // fix
                        tf :>> mapVal { tf => Type.fix(tf.vmap(Left(_))) }
                      case Left(x) =>
                        x switch {
                          case Right(tf |*| a) => // apply1
                            (tf ** outputX(a)) :>> mapVal { case (f, a) =>
                              f.vmap(Left(_))(a)
                            }
                          case Left(x) =>
                            x switch {
                              case Right(x) => // string
                                x :>> constVal(Type.string)
                              case Left(x) =>
                                x switch {
                                  case Right(x) => // int
                                    x :>> constVal(Type.int)
                                  case Left(x) =>
                                    x switch {
                                      case Right(x) => // unit
                                        x :>> constVal(Type.unit)
                                      case Left(mismatch) =>
                                        mismatch :>> mapVal { case (t, u) => Type.typeMismatch(t, u) }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
      }

    def close[X](
      closeX: X -⚬ Done,
    ): NonAbstractTypeF[X] -⚬ Done =
      λ { t =>
        t switch {
          case Right(a |*| b) => join(closeX(a) |*| closeX(b))
          case Left(t) => t switch {
            case Right(a |*| b) => join(closeX(a) |*| closeX(b))
            case Left(t) => t switch {
              case Right(a |*| b) => join(closeX(a) |*| closeX(b))
              case Left(t) => t switch {
                case Right(f) => neglect(f)
                case Left(t) => t switch {
                  case Right(f |*| x) => join(neglect(f) |*| closeX(x))
                  case Left(t) => t switch {
                    case Right(x) => x
                    case Left(t) => t switch {
                      case Right(x) => x
                      case Left(t) => t switch {
                        case Right(x) => x
                        case Left(e) => neglect(e)
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }

    def awaitPosFst[X](
      g: (Done |*| X) -⚬ X,
    ): (Done |*| NonAbstractTypeF[X]) -⚬ NonAbstractTypeF[X] =
      λ { case d |*| t =>
        t switch {
          case Right(a |*| b) => pair(g(d |*| a) |*| b)
          case Left(t) => t switch {
            case Right(a |*| b) => either(g(d |*| a) |*| b)
            case Left(t) => t switch {
              case Right(a |*| b) => recCall(g(d |*| a) |*| b)
              case Left(t) => t switch {
                case Right(f) => fix(f waitFor d)
                case Left(t) => t switch {
                  case Right(f |*| x) =>
                    apply1(f.waitFor(d) |*| x)
                  case Left(t) => t switch {
                    case Right(x) => string(join(d |*| x))
                    case Left(t) => t switch {
                      case Right(x) => int(join(d |*| x))
                      case Left(t) => t switch {
                        case Right(x) => unit(join(d |*| x))
                        case Left(e) => mismatch(e waitFor d)
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }

    given junctionNonAbstractType[X](using
      X: Junction.Positive[X],
    ): Junction.Positive[NonAbstractTypeF[X]] with {
      override def awaitPosFst: (Done |*| NonAbstractTypeF[X]) -⚬ NonAbstractTypeF[X] =
        NonAbstractType.awaitPosFst[X](X.awaitPosFst)
    }
  }

  object ConcreteType {
    def pack[T]: (NonAbstractTypeF[ConcreteType[T]] |+| TypeParamF[T]) -⚬ ConcreteType[T] =
      dsl.pack[ConcreteTypeF[T, _]]

    def unpack[T]: ConcreteType[T] -⚬ (NonAbstractTypeF[ConcreteType[T]] |+| TypeParamF[T]) =
      dsl.unpack

    def nonAbstractType[T]: NonAbstractTypeF[ConcreteType[T]] -⚬ ConcreteType[T] =
      pack ∘ injectL

    def typeParam[T]: TypeParamF[T] -⚬ ConcreteType[T] =
      pack ∘ injectR

    def pair[T]: (ConcreteType[T] |*| ConcreteType[T]) -⚬ ConcreteType[T] =
      NonAbstractType.pair > nonAbstractType

    def either[T]: (ConcreteType[T] |*| ConcreteType[T]) -⚬ ConcreteType[T] =
      NonAbstractType.either > nonAbstractType

    def recCall[T]: (ConcreteType[T] |*| ConcreteType[T]) -⚬ ConcreteType[T] =
      NonAbstractType.recCall > nonAbstractType

    def fix[T]: Val[TypeTagF] -⚬ ConcreteType[T] =
      NonAbstractType.fix > nonAbstractType

    def fixT[T, F[_]](F: TypeTag[F]): One -⚬ ConcreteType[T] =
      NonAbstractType.fixT(F) > nonAbstractType

    def string[T]: Done -⚬ ConcreteType[T] =
      NonAbstractType.string > nonAbstractType

    def int[T]: Done -⚬ ConcreteType[T] =
      NonAbstractType.int > nonAbstractType

    def unit[T]: Done -⚬ ConcreteType[T]=
      NonAbstractType.unit > nonAbstractType

    def mismatch[T]: Val[(Type, Type)] -⚬ ConcreteType[T] =
      NonAbstractType.mismatch > nonAbstractType

    def apply1T[T, F[_]](F: TypeTag[F]): ConcreteType[T] -⚬ ConcreteType[T] =
      apply1(TypeTag.toTypeFun(F))

    def apply1[T](f: TypeTagF): ConcreteType[T] -⚬ ConcreteType[T] = {
      λ { t => NonAbstractType.apply1(constantVal(f) |*| t) :>> nonAbstractType }
      // val ct = compilationTarget[T]
      // import ct.Map_●
      // f.compile(Map_●)(ct.typeAlgebra, Map_●).get(Map_●, Map_●) > awaitPosFst
    }

    class compilationTarget[T] {
      type Arr[K, L] = K -⚬ (Done |*| L)

      val category: SymmetricMonoidalCategory[Arr, |*|, One] =
        new SymmetricMonoidalCategory[Arr, |*|, One] {

          override def id[A]: Arr[A, A] =
            dsl.introFst(done)

          override def introFst[A]: Arr[A, One |*| A] =
            dsl.andThen(dsl.introFst, dsl.introFst(done))

          override def introSnd[A]: Arr[A, A |*| One] =
            dsl.andThen(dsl.introSnd, dsl.introFst(done))

          override def elimFst[A]: Arr[One |*| A, A] =
            dsl.fst(done)

          override def elimSnd[A]: Arr[A |*| One, A] =
            dsl.andThen(dsl.swap, dsl.fst(done))

          override def assocRL[A, B, C]: Arr[A |*| (B |*| C), (A |*| B) |*| C] =
            dsl.andThen(dsl.assocRL, dsl.introFst(done))

          override def assocLR[A, B, C]: Arr[(A |*| B) |*| C, A |*| (B |*| C)] =
            dsl.andThen(dsl.assocLR, dsl.introFst(done))

          override def swap[A, B]: Arr[A |*| B, B |*| A] =
            dsl.andThen(dsl.swap, dsl.introFst(done))

          override def andThen[A, B, C](
            f: Arr[A, B],
            g: Arr[B, C],
          ): Arr[A, C] =
            dsl.andThen(
              dsl.andThen(f, dsl.snd(g)),
              dsl.andThen(dsl.assocRL, dsl.fst(join)),
            )

          override def par[A1, A2, B1, B2](
            f1: Arr[A1, B1],
            f2: Arr[A2, B2],
          ): Arr[A1 |*| A2, B1 |*| B2] =
            dsl.andThen(
              dsl.par(f1, f2),
              λ { case (d1 |*| b1) |*| (d2 |*| b2) =>
                join(d1 |*| d2) |*| (b1 |*| b2)
              },
            )
        }

      val typeAlgebra: TypeAlgebra.Of[AbstractTypeLabel, Arr, ConcreteType[T], |*|, One] =
        new TypeAlgebra[AbstractTypeLabel, Arr] {
          override type Type = ConcreteType[T]
          override type <*>[A, B] = A |*| B
          override type None = One

          override def unit: Arr[One, ConcreteType[T]] =
            done > λ { case +(d) => d |*| ConcreteType.unit(d) }
          override def int: Arr[One, ConcreteType[T]] =
            done > λ { case +(d) => d |*| ConcreteType.int(d) }
          override def string: Arr[One, ConcreteType[T]] =
            done > λ { case +(d) => d |*| ConcreteType.string(d) }
          override def pair: Arr[ConcreteType[T] |*| ConcreteType[T], ConcreteType[T]] =
            λ { case t |*| u => constant(done) |*| ConcreteType.pair(t |*| u) }
          override def sum: Arr[ConcreteType[T] |*| ConcreteType[T], ConcreteType[T]] =
            λ { case t |*| u => constant(done) |*| ConcreteType.either(t |*| u) }
          override def recCall: Arr[ConcreteType[T] |*| ConcreteType[T], ConcreteType[T]] =
            λ { case t |*| u => constant(done) |*| ConcreteType.recCall(t |*| u) }
          override def fix(f: TypeFun[●, ●]): Arr[One, ConcreteType[T]] =
            // const(f) > ConcreteType.fix > introFst(done)
            ???
          override def abstractTypeName(name: AbstractTypeLabel): Arr[One, ConcreteType[T]] =
            throw NotImplementedError(s"TODO (${summon[SourcePos]})")

          override given category: SymmetricMonoidalCategory[Arr, |*|, One] =
            compilationTarget.this.category
        }

      sealed trait as[K, Q]

      case object Map_○ extends as[○, One]
      case object Map_● extends as[●, ConcreteType[T]]
      case class Pair[K1, K2, Q1, Q2](
        f1: K1 as Q1,
        f2: K2 as Q2,
      ) extends as[K1 × K2, Q1 |*| Q2]

      given objectMap: MonoidalObjectMap[as, ×, ○, |*|, One] =
        new MonoidalObjectMap[as, ×, ○, |*|, One] {

          override def uniqueOutputType[A, B, C](f: as[A, B], g: as[A, C]): B =:= C =
            (f, g) match {
              case (Map_○, Map_○) => summon[B =:= C]
              case (Map_●, Map_●) => summon[B =:= C]
              case (Pair(f1, f2), Pair(g1, g2)) =>
                (uniqueOutputType(f1, g1), uniqueOutputType(f2, g2)) match {
                  case (TypeEq(Refl()), TypeEq(Refl())) =>
                    summon[B =:= C]
                }
            }

          override def pair[A1, A2, X1, X2](f1: as[A1, X1], f2: as[A2, X2]): as[A1 × A2, X1 |*| X2] =
            Pair(f1, f2)

          override def unpair[A1, A2, X](f: as[A1 × A2, X]): Unpaired[A1, A2, X] =
            f match {
              case Pair(f1, f2) => Unpaired.Impl(f1, f2)
            }

          override def unit: as[○, One] =
            Map_○
        }
    }

    def abstractify[T](
      instantiate: ReboundType[T] -⚬ T,
    ): ConcreteType[T] -⚬ TypeEmitter[T] = rec { self =>
      unpack > dsl.either(
        NonAbstractType.map(self) > TypeEmitter.nonAbstractType[T],
        λ { case lbl |*| nt =>
          (lbl |*| nt) :>> TypeEmitter.genericType(instantiate)
        },
      )
    }

    def merge[T](
      instantiate: ReboundType[T] -⚬ T,
      splitT: T -⚬ (T |*| T),
      neglectT: T -⚬ Done,
      neglectNT: -[T] -⚬ Done,
      mergeInTX: (T |*| TypeEmitter[T]) -⚬ ReboundType[T],
    ): (ConcreteType[T] |*| ConcreteType[T]) -⚬ ConcreteType[T] =
      val abstractify = ConcreteType.abstractify(instantiate)
      par(abstractify, abstractify) > TypeEmitter.merge(
        instantiate,
        splitT,
        neglectT,
        neglectNT,
        mergeInTX,
      ) > TypeEmitter.generify
      // rec { self =>
      //   par(unpack, unpack) > λ { case a |*| b =>
      //     a switch {
      //       case Left(a) =>
      //         b switch {
      //           case Left(b) =>
      //             (a |*| b) :>> NonAbstractType.merge(self, output) :>> nonAbstractType
      //           case Right(bLbl |*| u) =>
      //             val a1 |*| a2 = a :>> NonAbstractType.split(split)
      //             returning(
      //               nonAbstractType(a1),
      //               makeT(a2) supplyTo u,
      //             )
      //         }
      //       case Right(aLbl |*| nt) =>
      //         b switch {
      //           case Left(b) =>
      //             val b1 |*| b2 = b :>> NonAbstractType.split(split)
      //             returning(
      //               nonAbstractType(b1)
      //             )
      //           case Right(bLbl |*| nu) =>
      //             ???
      //         }
      //     }
      //   }
      // }

    def split[T]: ConcreteType[T] -⚬ (ConcreteType[T] |*| ConcreteType[T]) =
      ???

    def isPair[T]: ConcreteType[T] -⚬ (ConcreteType[T] |+| (ConcreteType[T] |*| ConcreteType[T])) =
      unpack > dsl.either(
        NonAbstractType.isPair > |+|.lmap(nonAbstractType),
        typeParam > injectL,
      )

    def isRecCall[T]: ConcreteType[T] -⚬ (ConcreteType[T] |+| (ConcreteType[T] |*| ConcreteType[T])) =
      unpack > dsl.either(
        NonAbstractType.isRecCall > |+|.lmap(nonAbstractType),
        typeParam > injectL,
      )

    def output[T]: ConcreteType[T] -⚬ Val[Type] = rec { self =>
      λ { t =>
        unpack(t) switch {
          case Left(t) => t :>> NonAbstractType.output(self)
          case Right(lbl |*| nt) => ???
        }
      }
    }

    given junctionConcreteType[T]: Junction.Positive[ConcreteType[T]] with {
      override def awaitPosFst: (Done |*| ConcreteType[T]) -⚬ ConcreteType[T] =
        rec { self =>
          λ { case d |*| a =>
            unpack(a) switch {
              case Left(t) =>
                NonAbstractType.awaitPosFst(self)(d |*| t) :>> nonAbstractType
              case Right(lbl |*| t) =>
                (lbl.waitFor(d) |*| t) :>> typeParam
            }
          }
        }
    }
  }

  object DegenericType {
    def pack: (NonAbstractTypeF[DegenericType] |+| Val[AbstractTypeLabel]) -⚬ DegenericType =
      dsl.pack[DegenericTypeF]

    def unpack: DegenericType -⚬ (NonAbstractTypeF[DegenericType] |+| Val[AbstractTypeLabel]) =
      dsl.unpack

    def nonAbstractType: NonAbstractTypeF[DegenericType] -⚬ DegenericType =
      injectL > pack

    def abstractType: Val[AbstractTypeLabel] -⚬ DegenericType =
      injectR > pack

    val output: DegenericType -⚬ Val[Type] = rec { self =>
      unpack > either(
        NonAbstractType.output(self),
        mapVal { lbl => Type.abstractType(Right(lbl)) },
      )
    }

    val neglect: DegenericType -⚬ Done =
      output > dsl.neglect
  }

  object TypeSkelet {
    def map[T, Y, X, Q](f: X -⚬ Q): TypeSkelet[T, Y, X] -⚬ TypeSkelet[T, Y, Q] =
      λ { t =>
        t switch {
          case Left(t)  => t :>> NonAbstractType.map(f) :>> injectL
          case Right(t) => t :>> snd(RefinementRequest.map(f)) :>> injectR
        }
      }

    def contramap[T, Y, X, P](f: P -⚬ Y): TypeSkelet[T, Y, X] -⚬ TypeSkelet[T, P, X] =
      λ { t =>
        t switch {
          case Left(t)  => t :>> injectL
          case Right(t) => t :>> snd(RefinementRequest.contramap(f)) :>> injectR
        }
      }

    def dimap[T, Y, X, P, Q](f: P -⚬ Y, g: X -⚬ Q): TypeSkelet[T, Y, X] -⚬ TypeSkelet[T, P, Q] =
      contramap(f) > map(g)

    def abstractType[T, Y, X]: (Val[AbstractTypeLabel] |*| -[ReboundF[T, Y, X]]) -⚬ TypeSkelet[T, Y, X] =
      injectR

    def makeAbstractType[T, Y, X]: Val[AbstractTypeLabel] -⚬ (TypeSkelet[T, Y, X] |*| ReboundF[T, Y, X]) =
      λ { lbl =>
        val req |*| resp = constant(demand[ReboundF[T, Y, X]])
        abstractType(lbl |*| req) |*| resp
      }

    def nonAbstractType[T, Y, X]: NonAbstractTypeF[X] -⚬ TypeSkelet[T, Y, X] =
      injectL

    def newAbstractType[T, Y, X](v: AbstractTypeLabel)(
      mergeY: (Y |*| Y) -⚬ Y,
      outputY: Y -⚬ Val[Type],
      tapFlop: Y -⚬ (Y |*| X),
      mergeT: (T |*| T) -⚬ T,
      outputT: (Val[AbstractTypeLabel] |*| T) -⚬ Val[Type],
    ): One -⚬ (TypeSkelet[T, Y, X] |*| Val[Type] |*| TypeSkelet[T, Y, X]) =
      λ.* { _ =>
        producing { case tl |*| t |*| tr =>
          ((abstractType[T, Y, X] >>: tl) |*| (abstractType[T, Y, X] >>: tr)) match {
            case (lblL |*| recvL) |*| (lblR |*| recvR) =>
              returning(
                const(v) >>: lblL,
                const(v) >>: lblR,
                t := Rebound.unifyRebounds(v)(
                  mergeY,
                  outputY,
                  mergeT,
                  outputT,
                  tapFlop,
                )(recvL.asInput |*| recvR.asInput),
              )
          }
        }
      }

    def await[T, Y, X](
      awaitX: X -⚬ (NonAbstractTypeF[X] |+| (Val[AbstractTypeLabel] |*| -[T])),
    ): TypeSkelet[T, Y, X] -⚬ (NonAbstractTypeF[X] |+| (Val[AbstractTypeLabel] |*| -[T])) =
      λ { t =>
        t switch {
          case Left(t) =>
            injectL(t)
          case Right(lbl |*| req) =>
            RefinementRequest.decline(req) switch {
              case Left(x) => awaitX(x)
              case Right(t) => injectR(lbl |*| t)
            }
        }
      }

    def split[T, Y, X](
      splitX: X -⚬ (X |*| X),
      mergeY: (Y |*| Y) -⚬ Y,
      tapFlop: Y -⚬ (Y |*| X),
      mergeT: (T |*| T) -⚬ T,
    ): TypeSkelet[T, Y, X] -⚬ (TypeSkelet[T, Y, X] |*| TypeSkelet[T, Y, X]) =
      λ { t =>
        t switch {
          case Right(+(lbl) |*| req) => // abstract type
            val r1 |*| r2 = req :>> RefinementRequest.split(splitX, mergeY, tapFlop, mergeT)
            abstractType(lbl |*| r1) |*| abstractType(lbl |*| r2)
          case Left(t) =>
            t :>> NonAbstractType.split(splitX) :>> par(nonAbstractType, nonAbstractType)
        }
      }

    def mergeOp[T, Y, X](
      splitX: X -⚬ (X |*| X),
      mergeInXY: (X |*| Y) -⚬ X,
      makeX: TypeSkelet[T, Y, X] -⚬ X,
      tapFlop: Y -⚬ (Y |*| X),
      mergeY: (Y |*| Y) -⚬ Y,
      outputYApprox: Y -⚬ Val[Type],
      mergeT: (T |*| T) -⚬ T,
    )(using
      Junction.Positive[Y],
    ): (TypeSkelet[-[T], X, Y] |*| TypeSkelet[-[T], X, Y]) -⚬ TypeSkelet[-[T], X, Y] = {
      import NonAbstractType.junctionNonAbstractType

      λ { case a |*| b =>
        a switch {
          case Right(aLabel |*| aReq) => // `a` is abstract type
            b switch {
              case Right(bLabel |*| bReq) => // `b` is abstract type
                compareLabels(aLabel |*| bLabel) switch {
                  case Left(label) => // labels are same => neither refines the other
                    val req = RefinementRequest.merge(splitX)(aReq |*| bReq)
                    abstractType(label |*| req)
                  case Right(res) =>
                    res switch {
                      case Left(+(aLabel)) =>
                        val req1 |*| req2 = aReq :>> RefinementRequest.tapFlop(splitX, mergeInXY, tapFlop, mergeT)
                        returning(
                          abstractType(aLabel |*| req1),
                          RefinementRequest.completeWith(bReq |*| makeX(abstractType(aLabel |*| req2))),
                        )
                      case Right(+(bLabel)) =>
                        val req1 |*| req2 = bReq :>> RefinementRequest.tapFlop(splitX, mergeInXY, tapFlop, mergeT)
                        returning(
                          abstractType(bLabel |*| req1),
                          RefinementRequest.completeWith(aReq |*| makeX(abstractType(bLabel |*| req2))),
                        )
                    }
                }
              case Left(b) => // `b` is not abstract type
                val y |*| x = b :>> NonAbstractType.splitMap(tapFlop)
                returning(
                  nonAbstractType(y waitFor neglect(aLabel)),
                  RefinementRequest.completeWith(aReq |*| makeX(nonAbstractType(x))),
                )
            }
          case Left(a) => // `a` is not abstract type
            b switch {
              case Right(bLabel |*| bReq) => // `b` is abstract type
                val y |*| x = a :>> NonAbstractType.splitMap(tapFlop)
                returning(
                  nonAbstractType(y waitFor neglect(bLabel)),
                  RefinementRequest.completeWith(bReq |*| makeX(nonAbstractType(x))),
                )
              case Left(b) => // `b` is not abstract type
                nonAbstractType(NonAbstractType.merge(mergeY, outputYApprox)(a |*| b))
            }
        }
      }
    }

    def mergeFlip[T, Y, X](
      mergeX: (X |*| X) -⚬ X,
      splitX: X -⚬ (X |*| X),
      flipSplitX: X -⚬ (Y |*| Y),
      mergeFlipX: (X |*| X) -⚬ Y,
      newAbstractLink: One -⚬ (X |*| Y),
      instantiate: X -⚬ T,
      makeY: TypeSkelet[-[T], X, Y] -⚬ Y,
    ): (TypeSkelet[T, Y, X] |*| TypeSkelet[T, Y, X]) -⚬ TypeSkelet[-[T], X, Y] =
      λ { case a |*| b =>
        a switch {
          case Right(aLabel |*| aReq) => // `a` is abstract type
            b switch {
              case Right(bLabel |*| bReq) => // `b` is abstract type
                compareLabels(aLabel |*| bLabel) switch {
                  case Left(label) => // labels are same => neither refines the other
                    val req = RefinementRequest.mergeFlip(mergeX, splitX, flipSplitX, mergeFlipX, newAbstractLink, instantiate)(aReq |*| bReq)
                    abstractType(label |*| req)
                  case Right(res) =>
                    res switch {
                      case Left(+(aLabel)) =>
                        val req1 |*| req2 = aReq :>> RefinementRequest.flopSplit
                        returning(
                          abstractType(aLabel |*| req1),
                          RefinementRequest.completeWith(bReq |*| makeY(abstractType[-[T], X, Y](aLabel |*| req2))),
                        )
                      case Right(+(bLabel)) =>
                        val req1 |*| req2 = bReq :>> RefinementRequest.flopSplit
                        returning(
                          abstractType(bLabel |*| req1),
                          RefinementRequest.completeWith(aReq |*| makeY(abstractType(bLabel |*| req2))),
                        )
                    }
                }
              case Left(b) => // `b` is not abstract type
                val b1 |*| b2 = b :>> NonAbstractType.flopSplit[Y, X]
                returning(
                  nonAbstractType(b1),
                  RefinementRequest.completeWith(aReq |*| makeY(nonAbstractType(b2))),
                )
            }
          case Left(a) => // `a` is not abstract type
            b switch {
              case Right(bLabel |*| bReq) => // `b` is abstract type
                val a1 |*| a2 = a :>> NonAbstractType.flopSplit[Y, X]
                returning(
                  nonAbstractType(a1),
                  RefinementRequest.completeWith(bReq |*| makeY(nonAbstractType(a2))),
                )
              case Left(b) => // `b` is not abstract type
                nonAbstractType(NonAbstractType.mergeFlip()(a |*| b))
            }
        }
      }

    def merge[T, Y, X](
      mergeX: (X |*| X) -⚬ X,
      splitY: Y -⚬ (Y |*| Y),
      tapFlipXY: X -⚬ (X |*| Y),
      makeX: TypeSkelet[  T , Y, X] -⚬ X,
      makeY: TypeSkelet[-[T], X, Y] -⚬ Y,
      makeT: Y -⚬ T,
      splitT: T -⚬ (T |*| T),
      outputXApprox: X -⚬ Val[Type],
    )(using
      Junction.Positive[X],
    ): (TypeSkelet[T, Y, X] |*| TypeSkelet[T, Y, X]) -⚬ X =
      λ { case a |*| b =>
        a switch {
          case Right(aLabel |*| aReq) => // `a` is abstract type
            b switch {
              case Right(bLabel |*| bReq) => // `b` is abstract type
                mergeAbstractTypes(mergeX, splitY, tapFlipXY, makeX, makeY, makeT, splitT)(//, makeP, makeQ, mergeP, tapFlipPQ, mergeInQP)(
                  (aLabel |*| aReq) |*| (bLabel |*| bReq)
                )
              case Left(b) => // `b` is not abstract type
                import NonAbstractType.junctionNonAbstractType
                val bx |*| by = b :>> NonAbstractType.splitMap[X, X, Y](tapFlipXY)
                returning(
                  makeX(nonAbstractType(bx waitFor neglect(aLabel))),
                  RefinementRequest.completeWith(aReq |*| makeY(nonAbstractType(by))),
                )
            }
          case Left(a) => // `a` is not abstract type
            b switch {
              case Right(bLabel |*| bReq) => // `b` is abstract type
                val ax |*| ay = a :>> NonAbstractType.splitMap[X, X, Y](tapFlipXY)
                returning(
                  makeX(nonAbstractType[T, Y, X](ax)) waitFor neglect(bLabel),
                  RefinementRequest.completeWith(bReq |*| makeY(nonAbstractType(ay))),
                )
              case Left(b) => // `b` is not abstract type
                makeX(nonAbstractType((a |*| b) :>> NonAbstractType.merge(mergeX, outputXApprox)))
            }
        }
      }

    def mergeAbstractTypes[T, Y, X](
      mergeX: (X |*| X) -⚬ X,
      splitY: Y -⚬ (Y |*| Y),
      tapFlipXY: X -⚬ (X |*| Y),
      makeX: TypeSkelet[  T , Y, X] -⚬ X,
      makeY: TypeSkelet[-[T], X, Y] -⚬ Y,
      makeT: Y -⚬ T,
      splitT: T -⚬ (T |*| T),
    )(using
      Junction.Positive[X],
    ): ((Label |*| RefinementRequestF[T, Y, X]) |*| (Label |*| RefinementRequestF[T, Y, X])) -⚬ X =
      λ { case (aLabel |*| aReq) |*| (bLabel |*| bReq) =>
        compareLabels(aLabel |*| bLabel) switch {
          case Left(label) => // labels are same => neither refines the other
            val x |*| resp = makeAbstractType[T, Y, X](label)
            returning(
              makeX(x),
              resp switch {
                case Left(y) =>
                  val y1 |*| y2 = splitY(y)
                  returning(
                    RefinementRequest.completeWith(aReq |*| y1),
                    RefinementRequest.completeWith(bReq |*| y2),
                  )
                case Right(value) =>
                  value switch {
                    case Left(outReq) =>
                      val a = RefinementRequest.decline(aReq)
                      val b = RefinementRequest.decline(bReq)
                      a switch {
                        case Left(x1) =>
                          b switch {
                            case Left(x2) =>
                              injectL(mergeX(x1 |*| x2)) supplyTo outReq
                            case Right(nt) =>
                              val x |*| y = tapFlipXY(x1)
                              returning(
                                injectL(x) supplyTo outReq,
                                makeT(y) supplyTo nt,
                              )
                          }
                        case Right(nt1) =>
                          b switch {
                            case Left(x2) =>
                              val x |*| y = tapFlipXY(x2)
                              returning(
                                injectL(x) supplyTo outReq,
                                makeT(y) supplyTo nt1,
                              )
                            case Right(nt2) =>
                              val --(t) = outReq contramap injectR
                              val t1 |*| t2 = splitT(t)
                              returning(
                                t1 supplyTo nt1,
                                t2 supplyTo nt2,
                              )
                          }
                      }
                    case Right(?(_)) =>
                      (aReq |*| bReq) :>> crashNow(s"TODO: eliminate impossible case (${summon[SourcePos]})")
                  }
              },
            )
          case Right(res) =>
            def go: (Label |*| RefinementRequestF[T, Y, X] |*| RefinementRequestF[T, Y, X]) -⚬ X =
              λ { case +(aLabel) |*| aReq |*| bReq =>
                val y |*| resp = makeAbstractType[-[T], X, Y](aLabel)
                returning(
                  resp switch {
                    case Left(x) =>
                      val x1 |*| y1 = tapFlipXY(x)
                      returning(
                        x1 waitFor neglect(aLabel),
                        RefinementRequest.completeWith(aReq |*| y1),
                      )
                    case Right(b) =>
                      b switch {
                        case Right(?(_)) =>
                          (aLabel |*| aReq) :>> crashNow(s"TODO: eliminate ${summon[SourcePos]}")
                        case Left(bReq1) =>
                          val x |*| resp = makeAbstractType[T, Y, X](aLabel)
                          returning(
                            makeX(x),
                            resp switch {
                              case Left(y) =>
                                val y1 |*| y2 = splitY(y)
                                returning(
                                  RefinementRequest.completeWith(aReq |*| y1),
                                  injectL(y2) supplyTo bReq1,
                                )
                              case Right(value) =>
                                value switch {
                                  case Right(?(_)) =>
                                    (aReq |*| bReq1) :>> crashNow(s"TODO: eliminate ${summon[SourcePos]}")
                                  case Left(outReq) =>
                                    RefinementRequest.decline(aReq) switch {
                                      case Left(res) =>
                                        val x1 |*| y1 = tapFlipXY(res)
                                        returning(
                                          injectL(x1) supplyTo outReq,
                                          injectL(y1) supplyTo bReq1,
                                        )
                                      case Right(nt) =>
                                        val --(nt1) = bReq1 contramap injectR
                                        val --(t) = outReq contramap injectR
                                        val (t1 |*| t2) = splitT(t)
                                        returning(
                                          t1 supplyTo nt,
                                          t2 supplyTo nt1,
                                        )
                                    }
                                }
                            }
                          )
                      }
                  },
                  RefinementRequest.completeWith(bReq |*| makeY(y)),
                )
              }

            res switch {
              case Left(+(aLabel)) =>
                go(aLabel |*| aReq |*| bReq)
              case Right(+(bLabel)) =>
                go(bLabel |*| bReq |*| aReq)
            }
        }
      }

    def mergeOpWith[P, Q, Y, X](
      splitX: X -⚬ (X |*| X),
      mergeInXY: (X |*| Y) -⚬ X,
      tapFlopYX: Y -⚬ (Y |*| X),
      mergeP: (P |*| P) -⚬ P,
      makeX: TypeSkelet[P, Y, X] -⚬ X,
      makeY: TypeSkelet[Q, X, Y] -⚬ Y,
      xFillQ: (X |*| -[Q]) -⚬ X,
      yFlopFillP: (Y |*| -[P]) -⚬ X,
      tapFlipPQ: P -⚬ (P |*| Q),
      mergeInQP: (Q |*| P) -⚬ Q,
      outputXApprox: X -⚬ Val[Type],
      outputYApprox: Y -⚬ Val[Type],
    )(using
      Junction.Positive[X],
    ): (TypeSkelet[P, Y, X] |*| TypeSkelet[Q, X, Y]) -⚬ X =
      λ { case a |*| b =>
        a switch {
          case Right(aLabel |*| aReq) => // `a` is abstract type
            b switch {
              case Right(bLabel |*| bReq) => // `b` is abstract type
                mergeAbstractTypesOp(splitX, mergeInXY, tapFlopYX, makeX, makeY, xFillQ, yFlopFillP, mergeP, tapFlipPQ, mergeInQP)(
                  (aLabel |*| aReq) |*| (bLabel |*| bReq)
                )
              case Left(b) => // `b` is not abstract type
                import NonAbstractType.junctionNonAbstractType
                val by |*| bx = b :>> NonAbstractType.splitMap[Y, Y, X](tapFlopYX)
                returning(
                  makeX(nonAbstractType(bx waitFor neglect(aLabel))),
                  RefinementRequest.completeWith(aReq |*| makeY(nonAbstractType(by))),
                )
            }
          case Left(a) => // `a` is not abstract type
            b switch {
              case Right(bLabel |*| bReq) => // `b` is abstract type
                val a1 |*| a2 = a :>> NonAbstractType.split(splitX)
                val x = makeX(nonAbstractType[P, Y, X](a1)) waitFor neglect(bLabel)
                returning(
                  makeX(nonAbstractType(a2)),
                  RefinementRequest.completeWith(bReq |*| x),
                )
              case Left(b) => // `b` is not abstract type
                makeX(nonAbstractType((a |*| b) :>> NonAbstractType.mergeWith(mergeInXY, outputXApprox, outputYApprox)))
            }
        }
      }

    def mergeAbstractTypesOp[P, Q, Y, X](
      splitX: X -⚬ (X |*| X),
      mergeInXY: (X |*| Y) -⚬ X,
      tapFlopYX: Y -⚬ (Y |*| X),
      makeX: TypeSkelet[P, Y, X] -⚬ X,
      makeY: TypeSkelet[Q, X, Y] -⚬ Y,
      xFillQ: (X |*| -[Q]) -⚬ X,
      yFlopFillP: (Y |*| -[P]) -⚬ X,
      mergeP: (P |*| P) -⚬ P,
      tapFlipPQ: P -⚬ (P |*| Q),
      mergeInQP: (Q |*| P) -⚬ Q,
    )(using
      Junction.Positive[X],
    ): ((Label |*| RefinementRequestF[P, Y, X]) |*| (Label |*| RefinementRequestF[Q, X, Y])) -⚬ X =
      λ { case
        (aLabel |*| aReq)
        |*|
        (bLabel |*| bReq) =>
        compareLabels(aLabel |*| bLabel) switch {
          case Left(label) => // labels are same => neither refines the other
            // TODO: Can it even legally happen that the same
            //       abstract type is being merged in opposite polarities?
            val x |*| resp = makeAbstractType[P, Y, X](label)
            returning(
              makeX(x),
              resp switch {
                case Left(y) =>
                  val y1 |*| x1 = tapFlopYX(y)
                  returning(
                    RefinementRequest.completeWith(aReq |*| y1),
                    RefinementRequest.completeWith(bReq |*| x1),
                  )
                case Right(value) =>
                  value switch {
                    case Left(outReq) =>
                      val a = RefinementRequest.decline(aReq)
                      val b = RefinementRequest.decline(bReq)
                      a switch {
                        case Left(x) =>
                          b switch {
                            case Left(y) =>
                              injectL(mergeInXY(x |*| y)) supplyTo outReq
                            case Right(nq) =>
                              injectL(xFillQ(x |*| nq)) supplyTo outReq
                          }
                        case Right(np) =>
                          b switch {
                            case Left(y) =>
                              injectL(yFlopFillP(y |*| np)) supplyTo outReq
                            case Right(nq) =>
                              val --(p) = outReq contramap injectR
                              val p1 |*| q1 = tapFlipPQ(p)
                              returning(
                                p1 supplyTo np,
                                q1 supplyTo nq,
                              )
                          }
                      }
                    case Right(?(_)) =>
                      (aReq |*| bReq) :>> crashNow(s"TODO: is this case ever used? (${summon[SourcePos]})")
                  }
              },
            )
          case Right(res) =>
            res switch {
              case Left(+(aLabel)) =>
                val x |*| resp = makeAbstractType[P, Y, X](aLabel)
                returning(
                  resp switch {
                    case Left(y) =>
                      val y1 |*| x1 = tapFlopYX(y)
                      returning(
                        x1 waitFor neglect(aLabel),
                        RefinementRequest.completeWith(aReq |*| y1),
                      )
                    case Right(b) =>
                      b switch {
                        case Right(?(_)) =>
                          (aLabel |*| aReq) :>> crashNow(s"TODO: eliminate ${summon[SourcePos]}")
                        case Left(bReq1) =>
                          val x |*| resp = makeAbstractType[P, Y, X](aLabel)
                          returning(
                            makeX(x),
                            resp switch {
                              case Left(y) =>
                                val y1 |*| x1 = tapFlopYX(y)
                                returning(
                                  RefinementRequest.completeWith(aReq |*| y1),
                                  injectL(x1) supplyTo bReq1,
                                )
                              case Right(value) =>
                                value switch {
                                  case Right(?(_)) =>
                                    (aReq |*| bReq1) :>> crashNow(s"TODO: eliminate ${summon[SourcePos]}")
                                  case Left(outReq) =>
                                    RefinementRequest.decline(aReq) switch {
                                      case Left(res) =>
                                        val x1 |*| x2 = splitX(res)
                                        returning(
                                          injectL(x1) supplyTo outReq,
                                          injectL(x2) supplyTo bReq1,
                                        )
                                      case Right(np) =>
                                        val --(p1) = bReq1 contramap injectR
                                        val --(p2) = outReq contramap injectR
                                        mergeP(p1 |*| p2) supplyTo np
                                    }
                                }
                            }
                          )
                      }
                  },
                  RefinementRequest.completeWith(bReq |*| makeX(x)),
                )
              case Right(+(bLabel)) =>
                val y |*| resp = makeAbstractType[Q, X, Y](bLabel)
                returning(
                  resp switch {
                    case Left(x) =>
                      val x1 |*| x2 = splitX(x)
                      returning(
                        x1 waitFor neglect(bLabel),
                        RefinementRequest.completeWith(bReq |*| x2),
                      )
                    case Right(a) =>
                      a switch {
                        case Right(?(_)) =>
                          (bLabel |*| bReq) :>> crashNow(s"TODO: eliminate ${summon[SourcePos]}")
                        case Left(aReq1) =>
                          val x |*| resp = makeAbstractType[P, Y, X](bLabel)
                          returning(
                            makeX(x),
                            resp switch {
                              case Left(y) =>
                                val y1 |*| x1 = tapFlopYX(y)
                                returning(
                                  RefinementRequest.completeWith(bReq |*| x1),
                                  injectL(y1) supplyTo aReq1,
                                )
                              case Right(value) =>
                                value switch {
                                  case Right(?(_)) =>
                                    (aReq1 |*| bReq) :>> crashNow(s"TODO: eliminate ${summon[SourcePos]}")
                                  case Left(outReq) =>
                                    RefinementRequest.decline(bReq) switch {
                                      case Left(res) =>
                                        val y1 |*| x1 = tapFlopYX(res)
                                        returning(
                                          injectL(y1) supplyTo aReq1,
                                          injectL(x1) supplyTo outReq,
                                        )
                                      case Right(nq) =>
                                        val --(p) = outReq contramap injectR
                                        val --(q) = aReq1 contramap injectR
                                        mergeInQP(q |*| p) supplyTo nq
                                    }
                                }
                            }
                          )
                      }
                  },
                  RefinementRequest.completeWith(aReq |*| makeY(y)),
                )
            }
        }
      }

    def mergeIn[T, Y, X](
      splitX: X -⚬ (X |*| X),
      mergeY: (Y |*| Y) -⚬ Y,
      mergeInXY: (X |*| Y) -⚬ X,
      mergeInXT: (X |*| T) -⚬ X,
      tapFlop: Y -⚬ (Y |*| X),
      yt: Y -⚬ T,
      mergeT: (T |*| T) -⚬ T,
      makeX: TypeSkelet[  T , Y, X] -⚬ X,
      makeY: TypeSkelet[-[T], X, Y] -⚬ Y,
      outputXApprox: X -⚬ Val[Type],
      outputYApprox: Y -⚬ Val[Type],
    )(using
      Junction.Positive[X],
    ): (TypeSkelet[T, Y, X] |*| TypeSkelet[-[T], X, Y]) -⚬ TypeSkelet[T, Y, X] =
      λ { case a |*| b =>
        a switch {
          case Right(aLabel |*| aReq) => // `a` is abstract type
            b switch {
              case Right(bLabel |*| bReq) => // `b` is abstract type
                compareLabels(aLabel |*| bLabel) switch {
                  case Left(label) => // labels are same => neither refines the other
                    val req = (aReq |*| bReq) :>> RefinementRequest.mergeIn(tapFlop, mergeInXY, mergeInXT, yt, mergeT)
                    abstractType(label |*| req)
                  case Right(res) =>
                    res switch {
                      case Left(+(aLabel)) =>
                        val req1 |*| req2 = aReq :>> RefinementRequest.split(splitX, mergeY, tapFlop, mergeT)
                        returning(
                          abstractType(aLabel |*| req1),
                          RefinementRequest.completeWith(bReq |*| makeX(abstractType[T, Y, X](aLabel |*| req2))),
                        )
                      case Right(+(bLabel)) =>
                        val req1 |*| req2 = bReq :>> RefinementRequest.tapFlop(splitX, mergeInXY, tapFlop, mergeT)
                        returning(
                          abstractType(bLabel |*| req2),
                          RefinementRequest.completeWith(aReq |*| makeY(abstractType(bLabel |*| req1))),
                        )
                    }
                }
              case Left(b) => // `b` is not abstract type
                import NonAbstractType.junctionNonAbstractType
                val by |*| bx = b :>> NonAbstractType.splitMap[Y, Y, X](tapFlop)
                returning(
                  nonAbstractType(bx waitFor neglect(aLabel)),
                  RefinementRequest.completeWith(aReq |*| makeY(nonAbstractType(by))),
                )
            }
          case Left(a) => // `a` is not abstract type
            b switch {
              case Right(bLabel |*| bReq) => // `b` is abstract type
                val a1 |*| a2 = a :>> NonAbstractType.split(splitX)
                val x = makeX(nonAbstractType[T, Y, X](a1)) waitFor neglect(bLabel)
                returning(
                  nonAbstractType(a2),
                  RefinementRequest.completeWith(bReq |*| x),
                )
              case Left(b) => // `b` is not abstract type
                nonAbstractType((a |*| b) :>> NonAbstractType.mergeWith(mergeInXY, outputXApprox, outputYApprox))
            }
        }
      }

    def tapFlop[T, Y, X](
      splitX: X -⚬ (X |*| X),
      mergeInXY: (X |*| Y) -⚬ X,
      tapFlop: Y -⚬ (Y |*| X),
      mergeT: (T |*| T) -⚬ T,
    ): TypeSkelet[-[T], X, Y] -⚬ (TypeSkelet[-[T], X, Y] |*| TypeSkelet[T, Y, X]) =
      λ { t =>
        t switch {
          case Right(+(lbl) |*| req) =>
            val r1 |*| r2 = req :>> RefinementRequest.tapFlop(splitX, mergeInXY, tapFlop, mergeT)
            injectR(lbl |*| r1) |*| injectR(lbl |*| r2)
          case Left(a) => // NonAbstractType
            a :>> NonAbstractType.splitMap[Y, Y, X](tapFlop) :>> par(nonAbstractType, nonAbstractType)
        }
      }

    def tapFlip[T, Y, X](
      splitY: Y -⚬ (Y |*| Y),
      tapFlip: X -⚬ (X |*| Y),
      mergeInYX: (Y |*| X) -⚬ Y,
      splitT: T -⚬ (T |*| T),
    ): TypeSkelet[T, Y, X] -⚬ (TypeSkelet[T, Y, X] |*| TypeSkelet[-[T], X, Y]) =
      λ { t =>
        t switch {
          case Right(+(lbl) |*| req) => // abstract type
            val out1 |*| resp1 = makeAbstractType[T, Y, X](lbl)
            val out2 |*| resp2 = makeAbstractType[-[T], X, Y](lbl)
            returning(
              out1 |*| out2,
              resp1 switch {
                case Left(y) =>
                  resp2 switch {
                    case Left(x) =>
                      RefinementRequest.completeWith(req |*| mergeInYX(y |*| x))
                    case Right(value) =>
                      value switch {
                        case Left(out2Req) =>
                          val y1 |*| y2 = splitY(y)
                          returning(
                            RefinementRequest.completeWith(req |*| y1),
                            injectL(y2) supplyTo out2Req,
                          )
                        case Right(?(_)) =>
                          (req |*| y) :>> crashNow(s"TODO: is this case ever used? (${summon[SourcePos]})")
                      }
                  }
                case Right(value) =>
                  value switch {
                    case Left(out1Req) =>
                      resp2 switch {
                        case Left(x) =>
                          val x1 |*| y1 = tapFlip(x)
                          returning(
                            RefinementRequest.completeWith(req |*| y1),
                            injectL(x1) supplyTo out1Req,
                          )
                        case Right(value) =>
                          value switch {
                            case Left(out2Req) =>
                              RefinementRequest.decline(req) switch {
                                case Left(x) =>
                                  val x1 |*| y1 = tapFlip(x)
                                  returning(
                                    injectL(x1) supplyTo out1Req,
                                    injectL(y1) supplyTo out2Req,
                                  )
                                case Right(nt0) =>
                                  val --(t) = out1Req contramap injectR
                                  val --(nt2) = out2Req contramap injectR
                                  val t1 |*| t2 = splitT(t)
                                  returning(
                                    t1 supplyTo nt0,
                                    t2 supplyTo nt2,
                                  )
                              }
                            case Right(?(_)) =>
                              (out1Req |*| req) :>> crashNow(s"TODO: is this case ever used? (${summon[SourcePos]})")
                          }
                      }
                    case Right(?(_)) =>
                      (resp2 |*| req) :>> crashNow(s"TODO: is this case ever used? (${summon[SourcePos]})")
                  }
              },
            )
          case Left(t) => // non-abstract type
            t :>> NonAbstractType.splitMap[X, X, Y](tapFlip) :>> par(nonAbstractType, nonAbstractType)
        }
      }

    def output[T, Y, X](
      outputX: X -⚬ Val[Type],
      outputNegT: (Label |*| -[T]) -⚬ Val[Type],
    ): TypeSkelet[T, Y, X] -⚬ Val[Type] =
      λ { _ switch {
        case Right(label |*| req) => // abstract type
          RefinementRequest.decline(req) switch {
            case Left(x)   => outputX(x) waitFor neglect(label)
            case Right(nt) => outputNegT(label |*| nt)
          }
        case Left(x) =>
          NonAbstractType.output(outputX)(x)
      }}

    def close[T, Y, X](
      neglectX: X -⚬ Done,
      neglectTypeParam: -[T] -⚬ Done,
    ): TypeSkelet[T, Y, X] -⚬ Done =
      λ { _ switch {
        case Right(label |*| req) => // abstract type
          joinAll(
            neglect(label),
            RefinementRequest.decline(req) switch {
              case Left(x)   => neglectX(x)
              case Right(nt) => neglectTypeParam(nt)
            },
          )
        case Left(x) =>
          NonAbstractType.close(neglectX)(x)
      }}

    def outputApprox[T, Y, X](
      outputXApprox: X -⚬ Val[Type],
      neglectTypeParam: -[T] -⚬ Done,
    ): TypeSkelet[T, Y, X] -⚬ Val[Type] =
      λ { _ switch {
        case Right(label |*| req) => // abstract type
          (label :>> mapVal(l => Type.abstractType(Right(l))))
            .waitFor {
              RefinementRequest.decline(req) switch {
                case Left(x) =>
                  outputXApprox(x) > neglect
                case Right(nt) =>
                  neglectTypeParam(nt)
              }
            }
        case Left(x) =>
          NonAbstractType.output(outputXApprox)(x)
      }}

    def generify[T, Y, X](
      wrapX: X -⚬ ConcreteType[T],
    ): TypeSkelet[T, Y, X] -⚬ ConcreteType[T] = {
      import ConcreteType.junctionConcreteType

      dsl.either(
        NonAbstractType.map(wrapX) > ConcreteType.nonAbstractType,
        λ { case lbl |*| req =>
          RefinementRequest.decline(req) switch {
            case Left(x)   => wrapX(x) waitFor neglect(lbl)
            case Right(nt) => ConcreteType.typeParam(lbl |*| nt)
          }
        },
      )
    }

    private type Label = Val[AbstractTypeLabel]

    private def compareLabels: (Label |*| Label) -⚬ (Label |+| (Label |+| Label)) =
      λ { case a |*| b =>
        (a ** b) :>> mapVal { case (a, b) =>
          (a.value compareTo b.value) match {
            case 0 => Left(a)
            case i if i < 0 => Right(Left(a))
            case i if i > 0 => Right(Right(b))
          }
        } :>> liftEither :>> |+|.rmap(liftEither)
      }

    def awaitPosFst[T, Y, X](
      g: (Done |*| X) -⚬ X,
    ): (Done |*| TypeSkelet[T, Y, X]) -⚬ TypeSkelet[T, Y, X] =
      λ { case d |*| t =>
        t switch {
          case Right(lbl |*| req) => injectR(lbl.waitFor(d) |*| req)
          case Left(t)            => (d |*| t) :>> NonAbstractType.awaitPosFst(g) :>> injectL
        }
      }
  }

  object TypeEmitterF {
    def pack[T, Y]: TypeSkelet[T, Y, TypeEmitterF[T, Y]] -⚬ TypeEmitterF[T, Y] =
      dsl.pack

    def unpack[T, Y]: TypeEmitterF[T, Y] -⚬ TypeSkelet[T, Y, TypeEmitterF[T, Y]] =
      dsl.unpack

    def contramap[T, Y, P](f: P -⚬ Y): TypeEmitterF[T, Y] -⚬ TypeEmitterF[T, P] =
      rec { self =>
        unpack[T, Y] > TypeSkelet.dimap(f, self) > pack[T, P]
      }
  }

  object TypeEmitter {

    private def pack0[T]: TypeEmitterF[T, ReboundTypeF[T, TypeEmitter[T]]] -⚬ TypeEmitter[T] =
      dsl.pack[[X] =>> TypeEmitterF[T, ReboundTypeF[T, X]]]

    private def unpack0[T]: TypeEmitter[T] -⚬ TypeEmitterF[T, ReboundTypeF[T, TypeEmitter[T]]] =
      dsl.unpack

    def pack1_[T](
      packRebound1: ReboundTypeF[T, TypeEmitter[T]] -⚬ ReboundType[T],
    ): TypeEmitterF[T, ReboundType[T]] -⚬ TypeEmitter[T] =
      TypeEmitterF.contramap(packRebound1) > pack0[T]

    private def pack1[T]: TypeEmitterF[T, ReboundType[T]] -⚬ TypeEmitter[T] =
      rec { self =>
        pack1_(ReboundType.pack1_(self))
      }

    def unpack1_[T](
      unpackRebound1: ReboundType[T] -⚬ ReboundTypeF[T, TypeEmitter[T]],
    ): TypeEmitter[T] -⚬ TypeEmitterF[T, ReboundType[T]] =
      unpack0[T] > TypeEmitterF.contramap(unpackRebound1)

    private def unpack1[T]: TypeEmitter[T] -⚬ TypeEmitterF[T, ReboundType[T]] =
      rec { self =>
        unpack1_(ReboundType.unpack1_(self))
      }

    def unpack[T]: TypeEmitter[T] -⚬ TypeSkelet[T, ReboundType[T], TypeEmitter[T]] =
      λ { t =>
        val t1: $[TypeEmitterF[T, ReboundType[T]]] = unpack1[T](t)
        val t2: $[TypeSkelet[T, ReboundType[T], TypeEmitterF[T, ReboundType[T]]]] = TypeEmitterF.unpack(t1)
        t2 :>> TypeSkelet.map(pack1)
      }

    def pack[T]: TypeSkelet[T, ReboundType[T], TypeEmitter[T]] -⚬ TypeEmitter[T] =
      λ { t =>
        val t1: $[TypeSkelet[T, ReboundType[T], TypeEmitterF[T, ReboundType[T]]]] = t :>> TypeSkelet.map(unpack1)
        val t2: $[TypeEmitterF[T, ReboundType[T]]] = TypeEmitterF.pack(t1)
        pack1(t2)
      }

    def unapply[T](using SourcePos)(a: $[TypeEmitter[T]])(using LambdaContext): Some[$[TypeSkelet[T, ReboundType[T], TypeEmitter[T]]]] =
      Some(unpack(a))

    def nonAbstractType[T]: NonAbstractTypeF[TypeEmitter[T]] -⚬ TypeEmitter[T] =
      TypeSkelet.nonAbstractType > pack

    def makeAbstractType[T]: Val[AbstractTypeLabel] -⚬ (TypeEmitter[T] |*| ReboundF[T, ReboundType[T], TypeEmitter[T]]) =
      TypeSkelet.makeAbstractType[T, ReboundType[T], TypeEmitter[T]] > fst(pack)

    def genericType[T](
      instantiate: ReboundType[T] -⚬ T,
    ): (Val[AbstractTypeLabel] |*| -[T]) -⚬ TypeEmitter[T] =
      λ { case lbl |*| nt =>
        val out |*| resp = makeAbstractType[T](lbl)
        returning(
          out,
          resp switch {
            case Left(y) =>
              instantiate(y) supplyTo nt
            case Right(value) =>
              value switch {
                case Left(outReq) =>
                  injectR(nt) supplyTo outReq
                case Right(?(_)) =>
                  nt :>> crashNow(s"TODO: Is this case really ever used? (${summon[SourcePos]})")
              }
          }
        )
      }

    def newAbstractType[T](v: AbstractTypeLabel)(
      mergeInT: (TypeEmitter[T] |*| T) -⚬ TypeEmitter[T],
      mergeT: (T |*| T) -⚬ T,
      makeT: ReboundType[T] -⚬ T,
      outputT: (Val[AbstractTypeLabel] |*| T) -⚬ Val[Type],
      neglectT: T -⚬ Done,
      neglectNT: -[T] -⚬ Done,
    ): One -⚬ (TypeEmitter[T] |*| Val[Type] |*| TypeEmitter[T]) =
      TypeSkelet.newAbstractType[T, ReboundType[T], TypeEmitter[T]](v)(
        ReboundType.merge(mergeInT, makeT, mergeT, neglectT, neglectNT),
        ReboundType.output(outputT),
        ReboundType.tapFlop(mergeInT, makeT, mergeT, neglectT, neglectNT),
        mergeT,
        outputT,
      )
        > λ { case a |*| t |*| b => pack(a) |*| t |*| pack(b) }

    // def abstractType[T, Y]: (Val[AbstractTypeLabel] |*| -[ReboundF[T, Y, TypeEmitterF[T, Y]]]) -⚬ TypeEmitterF[T, Y] =
    //   packF ∘ injectR

    // def nonAbstractType[T, Y]: NonAbstractTypeF[TypeEmitterF[T, Y]] -⚬ TypeEmitterF[T, Y] =
    //   packF ∘ injectL

    def expectPair[T]: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| TypeEmitter[T]) =
      throw NotImplementedError(s"at ${summon[SourcePos]}")

    def expectRecCall[T]: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| TypeEmitter[T]) =
      throw NotImplementedError(s"at ${summon[SourcePos]}")

    def split_[T](
      mergeInbound: (ReboundType[T] |*| ReboundType[T]) -⚬ ReboundType[T],
      tapFlop: ReboundType[T] -⚬ (ReboundType[T] |*| TypeEmitter[T]),
      mergeT: (T |*| T) -⚬ T,
    ): TypeEmitter[T] -⚬ (TypeEmitter[T] |*| TypeEmitter[T]) = rec { self =>
      unpack > TypeSkelet.split(self, mergeInbound, tapFlop, mergeT) > par(pack, pack)
    }

    def split[T](
      mergeInT: (TypeEmitter[T] |*| T) -⚬ TypeEmitter[T],
      makeT: ReboundType[T] -⚬ T,
      mergeT: (T |*| T) -⚬ T,
      neglectT: T -⚬ Done,
      neglectNT: -[T] -⚬ Done,
    ): TypeEmitter[T] -⚬ (TypeEmitter[T] |*| TypeEmitter[T]) =
      rec { self =>
        val mergeInbound =
          ReboundType.merge__(
            self,
            mergeIn(mergeInT, makeT, mergeT, neglectT, neglectNT),
            mergeInT,
            makeT,
            mergeT,
            neglectT,
            neglectNT,
          )

        split_(
          mergeInbound,
          ReboundType.tapFlop_(mergeInbound, mergeInT, makeT, mergeT, neglectT, neglectNT),
          mergeT,
        )
      }

    def tapFlip__[T](
      instantiate: ReboundType[T] -⚬ T,
      splitT: T -⚬ (T |*| T),
      mergeInTX: (T |*| TypeEmitter[T]) -⚬ ReboundType[T],
      splitRebound: ReboundType[T] -⚬ (ReboundType[T] |*| ReboundType[T]),
      mergeIntoRebound: (ReboundType[T] |*| TypeEmitter[T]) -⚬ ReboundType[T],
    ): TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]) = rec { self =>
      λ { case TypeEmitter(a) =>
        a :>> TypeSkelet.tapFlip(
          splitRebound,
          self,
          mergeIntoRebound,
          splitT,
        ) :>> par(pack, ReboundType.pack)
      }
    }

    def tapFlip_[T](
      instantiate: ReboundType[T] -⚬ T,
      splitT: T -⚬ (T |*| T),
      mergeInTX: (T |*| TypeEmitter[T]) -⚬ ReboundType[T],
      splitRebound: ReboundType[T] -⚬ (ReboundType[T] |*| ReboundType[T]),
      mergeIntoRebound: (ReboundType[T] |*| TypeEmitter[T]) -⚬ ReboundType[T],
    ): TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]) =
      tapFlip__(instantiate, splitT, mergeInTX, splitRebound, mergeIntoRebound)

    def tapFlip[T](
      instantiate: ReboundType[T] -⚬ T,
      splitT: T -⚬ (T |*| T),
      neglectT: T -⚬ Done,
      neglectNT: -[T] -⚬ Done,
      mergeInTX: (T |*| TypeEmitter[T]) -⚬ ReboundType[T],
    ): TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]) = rec { self =>
      val splitRebound: ReboundType[T] -⚬ (ReboundType[T] |*| ReboundType[T]) =
        rec { splitRebound =>
          ReboundType.split_(
            instantiate,
            splitT,
            mergeInTX,
            merge__(
              instantiate,
              splitT,
              neglectNT,
              mergeInTX,
              splitRebound,
              self,
            ),
            self,
          )
        }

      val mergeIntoRebound: (ReboundType[T] |*| TypeEmitter[T]) -⚬ ReboundType[T] =
        rec { mergeIntoRebound =>
          ReboundType.mergeIn_(
            instantiate,
            splitT,
            neglectT,
            neglectNT,
            mergeInTX,
            merge__(
              instantiate,
              splitT,
              neglectNT,
              mergeInTX,
              splitRebound,
              self,
            ),
            self,
          )
        }

      tapFlip_(
        instantiate,
        splitT,
        mergeInTX,
        splitRebound,
        mergeIntoRebound,
      )
    }

    def merge__[T](
      instantiate: ReboundType[T] -⚬ T,
      splitT: T -⚬ (T |*| T),
      neglectNT: -[T] -⚬ Done,
      mergeInTX: (T |*| TypeEmitter[T]) -⚬ ReboundType[T],
      splitRebound: ReboundType[T] -⚬ (ReboundType[T] |*| ReboundType[T]),
      tapFlip: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]),
    ): (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ TypeEmitter[T] = rec { self =>
      λ { case TypeEmitter(a) |*| TypeEmitter(b) =>
        TypeSkelet.merge(
          self,
          splitY = splitRebound,
          tapFlipXY = tapFlip,
          makeX = pack,
          makeY = ReboundType.pack,
          makeT = instantiate,
          splitT = splitT,
          outputApprox(neglectNT),
        )(a |*| b)
      }
    }

    def merge_[T](
      instantiate: ReboundType[T] -⚬ T,
      splitT: T -⚬ (T |*| T),
      neglectNT: -[T] -⚬ Done,
      mergeInTX: (T |*| TypeEmitter[T]) -⚬ ReboundType[T],
      splitRebound: ReboundType[T] -⚬ (ReboundType[T] |*| ReboundType[T]),
      mergeIntoRebound: (ReboundType[T] |*| TypeEmitter[T]) -⚬ ReboundType[T],
    ): (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ TypeEmitter[T] = rec { self =>
      merge__(
        instantiate,
        splitT,
        neglectNT,
        mergeInTX,
        splitRebound,
        tapFlip__(instantiate, splitT, mergeInTX, splitRebound, mergeIntoRebound),
      )
    }

    def merge[T](
      instantiate: ReboundType[T] -⚬ T,
      splitT: T -⚬ (T |*| T),
      neglectT: T -⚬ Done,
      neglectNT: -[T] -⚬ Done,
      mergeInTX: (T |*| TypeEmitter[T]) -⚬ ReboundType[T],
    ): (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ TypeEmitter[T] = rec { self =>
      val (mergeIntoRebound, splitRebound) =
        rec2 {
          (
            mergeIntoRebound: (ReboundType[T] |*| TypeEmitter[T]) -⚬ ReboundType[T],
            splitRebound: ReboundType[T] -⚬ (ReboundType[T] |*| ReboundType[T]),
          ) => {
            val tapFlip =
              tapFlip__(
                instantiate,
                splitT,
                mergeInTX,
                splitRebound,
                mergeIntoRebound,
              )
            (
              ReboundType.mergeIn_(instantiate, splitT, neglectT, neglectNT, mergeInTX, self, tapFlip),
              ReboundType.split_(instantiate, splitT, mergeInTX, self, tapFlip)
            )
          }
        }

      merge_(
        instantiate,
        splitT,
        neglectNT,
        mergeInTX,
        splitRebound,
        mergeIntoRebound,
      )
    }

    def mergeIn__[T](
      split: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| TypeEmitter[T]),
      mergeRebound: (ReboundType[T] |*| ReboundType[T]) -⚬ ReboundType[T],
      mergeInT: (TypeEmitter[T] |*| T) -⚬ TypeEmitter[T],
      tapFlop: ReboundType[T] -⚬ (ReboundType[T] |*| TypeEmitter[T]),
      yt: ReboundType[T] -⚬ T,
      mergeT: (T |*| T) -⚬ T,
      neglectT: T -⚬ Done,
      neglectNT: -[T] -⚬ Done,
    ): (TypeEmitter[T] |*| ReboundType[T]) -⚬ TypeEmitter[T] = rec { self =>
      λ { case a |*| b =>
        val a1: $[TypeSkelet[  T , ReboundType[T], TypeEmitter[T]]] = unpack(a)
        val b1: $[TypeSkelet[-[T], TypeEmitter[T], ReboundType[T]]] = ReboundType.unpack(b)
        (a1 |*| b1) :>> TypeSkelet.mergeIn(
          split,
          mergeRebound,
          self,
          mergeInT,
          tapFlop,
          yt,
          mergeT,
          pack,
          ReboundType.pack,
          outputApprox(neglectNT),
          ReboundType.outputApprox(neglectT),
        ) :>> pack
      }
    }

    def mergeIn_[T](
      mergeInbound: (ReboundType[T] |*| ReboundType[T]) -⚬ ReboundType[T],
      mergeInT: (TypeEmitter[T] |*| T) -⚬ TypeEmitter[T],
      tapFlop: ReboundType[T] -⚬ (ReboundType[T] |*| TypeEmitter[T]),
      makeT: ReboundType[T] -⚬ T,
      mergeT: (T |*| T) -⚬ T,
      neglectT: T -⚬ Done,
      neglectNT: -[T] -⚬ Done,
    ): (TypeEmitter[T] |*| ReboundType[T]) -⚬ TypeEmitter[T] =
      mergeIn__[T](
        split_(mergeInbound, tapFlop, mergeT),
        mergeInbound,
        mergeInT,
        tapFlop,
        makeT,
        mergeT,
        neglectT,
        neglectNT,
      )

    def mergeIn[T](
      mergeInT: (TypeEmitter[T] |*| T) -⚬ TypeEmitter[T],
      makeT: ReboundType[T] -⚬ T,
      mergeT: (T |*| T) -⚬ T,
      neglectT: T -⚬ Done,
      neglectNT: -[T] -⚬ Done,
    ): (TypeEmitter[T] |*| ReboundType[T]) -⚬ TypeEmitter[T] = rec { self =>
      val mergeInbound =
        ReboundType.merge_(
          self,
          mergeInT,
          makeT,
          mergeT,
          neglectT,
          neglectNT,
        )

      mergeIn_[T](
        mergeInbound,
        mergeInT,
        ReboundType.tapFlop_(mergeInbound, mergeInT, makeT, mergeT, neglectT, neglectNT),
        makeT,
        mergeT,
        neglectT,
        neglectNT,
      )
    }

    def mergeFlip[T](
      merge: (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ TypeEmitter[T],
      split: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| TypeEmitter[T]),
      flipSplit: TypeEmitter[T] -⚬ (ReboundType[T] |*| ReboundType[T]),
      newAbstractLink: One -⚬ (TypeEmitter[T] |*| ReboundType[T]),
      instantiate: TypeEmitter[T] -⚬ T,
    ): (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ ReboundType[T] = rec { self =>
      λ { case a |*| b =>
        val a1: $[TypeSkelet[T, ReboundType[T], TypeEmitter[T]]] = unpack(a)
        val b1: $[TypeSkelet[T, ReboundType[T], TypeEmitter[T]]] = unpack(b)
        val c: $[TypeSkelet[-[T], TypeEmitter[T], ReboundType[T]]] =
          (a1 |*| b1) :>> TypeSkelet.mergeFlip(merge, split, flipSplit, self, newAbstractLink, instantiate, ReboundType.pack)
        ReboundType.pack(c)
      }
    }

    def outputApprox[T](
      neglectTypeParam: -[T] -⚬ Done,
    ): TypeEmitter[T] -⚬ Val[Type] =
      rec { self =>
        unpack > TypeSkelet.outputApprox(self, neglectTypeParam)
      }

    def generify[T]: TypeEmitter[T] -⚬ ConcreteType[T] =
      rec { self =>
        unpack > TypeSkelet.generify(self)
      }

    // def disengage[T]: TypeEmitter[T] -⚬ Done = rec { self =>
    //   λ { case TypeEmitter(t) =>
    //     t switch {
    //       case Right(lbl |*| req) =>
    //         returning(
    //           neglect(lbl),
    //           RefinementRequest.decline0(req),
    //         )
    //       case Left(t) => t switch {
    //         case Right(a |*| b) => join(self(a) |*| self(b))
    //         case Left(t) => t switch {
    //           case Right(a |*| b) => join(self(a) |*| self(b))
    //           case Left(t) => t switch {
    //             case Right(a |*| b) => join(self(a) |*| self(b))
    //             case Left(t) => t switch {
    //               case Right(f) => neglect(f)
    //               case Left(t) => t switch {
    //                 case Right(f |*| x) => join(neglect(f) |*| self(x))
    //                 case Left(t) => t switch {
    //                   case Right(t) => t
    //                   case Left(t) => t switch {
    //                     case Right(t) => t
    //                     case Left(t) => t switch {
    //                       case Right(t) => t
    //                       case Left(t) => neglect(t)
    //                     }
    //                   }
    //                 }
    //               }
    //             }
    //           }
    //         }
    //       }
    //     }
    //   }
    // }

    def awaitPosFst[T]: (Done |*| TypeEmitter[T]) -⚬ TypeEmitter[T] =
      rec { self =>
        λ { case d |*| t =>
          (d |*| unpack(t)) :>> TypeSkelet.awaitPosFst(self) :>> pack
        }
      }

    given junctionTypeEmitter[T]: Junction.Positive[TypeEmitter[T]] with {
      override def awaitPosFst: (Done |*| TypeEmitter[T]) -⚬ TypeEmitter[T] =
        TypeEmitter.awaitPosFst
    }
  }

  type GenericType[T] = ConcreteType[T]

  type InboundType = Rec[[X] =>> Maybe[ReboundType[X]]]
  object InboundType {
    def pack: Maybe[ReboundType[InboundType]] -⚬ InboundType =
      dsl.pack[[X] =>> Maybe[ReboundType[X]]]

    def unpack: InboundType -⚬ Maybe[ReboundType[InboundType]] =
      dsl.unpack

    val just: ReboundType[InboundType] -⚬ InboundType =
      Maybe.just > pack

    def none: One -⚬ InboundType =
      Maybe.empty > pack

    def apply(using
      SourcePos,
      LambdaContext,
    )(a: $[Maybe[ReboundType[InboundType]]]): $[InboundType] =
      pack(a)

    def unapply(using
      SourcePos,
      LambdaContext,
    )(a: $[InboundType]): Some[$[Maybe[ReboundType[InboundType]]]] =
      Some(unpack(a))

    private def mergeTo_(
      merge: (InboundType |*| InboundType) -⚬ InboundType,
    ): (TypeEmitter[InboundType] |*| InboundType) -⚬ TypeEmitter[InboundType] = rec { self =>
      λ { case a |*| InboundType(b) =>
        Maybe.toEither(b) switch {
          case Left(?(_)) =>
            a
          case Right(b) =>
            (a |*| b) :>> TypeEmitter.mergeIn(self, just, merge, close, supplyNone)
        }
      }
    }

    val mergeTo: (TypeEmitter[InboundType] |*| InboundType) -⚬ TypeEmitter[InboundType] =
      mergeTo_(merge)

    def mergeIn_(
      split: InboundType -⚬ (InboundType |*| InboundType),
    ): (InboundType |*| TypeEmitter[InboundType]) -⚬ ReboundType[InboundType] =
      rec { self =>
        λ { case InboundType(a) |*| b =>
          Maybe.toEither(a) switch {
            case Left(?(_)) =>
              b :>> crashNow(s"Cannot implement TypeEmitter[InboundType] -⚬ ReboundType[InboundType] (${summon[SourcePos]})")
            case Right(a) =>
              (a |*| b) :>> ReboundType.mergeIn(just, split, close, supplyNone, self)
          }
        }
      }

    val mergeIn: (InboundType |*| TypeEmitter[InboundType]) -⚬ ReboundType[InboundType] =
      mergeIn_(split)

    val merge: (InboundType |*| InboundType) -⚬ InboundType =
      rec { self =>
        λ { case InboundType(a) |*| InboundType(b) =>
          Maybe.toEither(a) switch {
            case Left(?(_)) =>
              InboundType(b)
            case Right(a) =>
              Maybe.toEither(b) switch {
                case Left(?(_)) =>
                  InboundType(Maybe.just(a))
                case Right(b) =>
                  (a |*| b) :>> ReboundType.merge_(
                    TypeEmitter.mergeIn(mergeTo_(self), just, self, close, supplyNone),
                    mergeTo_(self),
                    just,
                    self,
                    close,
                    supplyNone,
                  ) :>> just
              }
          }
        }
      }

    val split: InboundType -⚬ (InboundType |*| InboundType) =
      rec { self =>
        λ { case InboundType(a) =>
          Maybe.toEither(a) switch {
            case Left(?(_)) =>
              constant(none) |*| constant(none)
            case Right(a) =>
              a :>> ReboundType.split(just, self, mergeIn_(self), close, supplyNone) :>> par(just, just)
          }
        }
      }

    def close: InboundType -⚬ Done =
      rec { self =>
        unpack > Maybe.toEither > dsl.either(
          done,
          ReboundType.close(self),
        )
      }

    def supplyNone: -[InboundType] -⚬ Done =
      introFst(none) > supply > done

    val output: (Val[AbstractTypeLabel] |*| InboundType) -⚬ Val[Type] =
      rec { self =>
        λ { case lbl |*| t =>
          Maybe.toEither(unpack(t)) switch {
            case Left(?(_)) =>
              lbl :>> mapVal { l => Type.abstractType(Right(l)) }
            case Right(t) =>
              (t :>> ReboundType.output(self))
                .waitFor(neglect(lbl))
          }
        }
      }
  }

  private val degenerify: GenericType[InboundType] -⚬ DegenericType =
    rec { self =>
      ConcreteType.unpack > either(
        NonAbstractType.map(self) > DegenericType.nonAbstractType,
        λ { case lbl |*| p =>
          returning(
            DegenericType.abstractType(lbl),
            constant(InboundType.none) supplyTo p,
          )
        },
      )
    }

  def inferTypes[A, B](f: Fun[A, B]): One -⚬ Val[TypedFun[A, B]] = {
    println(s"inferTypes($f)")
    val t0 = System.currentTimeMillis()

    given VarGen[State[Int, *], AbstractTypeLabel] with {
      override def newVar: State[Int, AbstractTypeLabel] =
        State(n => (n+1, AbstractTypeLabel(n)))
    }

    val res =
    reconstructTypes[InboundType, A, B, State[Int, *]](f)(
      InboundType.mergeTo,
      InboundType.mergeIn,
      InboundType.merge,
      InboundType.split,
      InboundType.just,
      InboundType.output,
      InboundType.close,
      InboundType.supplyNone,
      degenerify,
    )
      .map { prg =>
        prg > λ { case a |*| f |*| b =>
          f
            .waitFor(a :>> degenerify :>> DegenericType.neglect)
            .waitFor(b :>> degenerify :>> DegenericType.neglect)
        }
      }
      .run(0)

    val t1 = System.currentTimeMillis()
    println(s"inferTypes assembly took ${t1 - t0}ms")
    res
  }

  def reconstructTypes[T, A, B, M[_]](f: Fun[A, B])(
    mergeInT: (TypeEmitter[T] |*| T) -⚬ TypeEmitter[T],
    mergeIntoT: (T |*| TypeEmitter[T]) -⚬ ReboundType[T],
    mergeT: (T |*| T) -⚬ T,
    splitT: T -⚬ (T |*| T),
    makeT: ReboundType[T] -⚬ T,
    outputT: (Val[AbstractTypeLabel] |*| T) -⚬ Val[Type],
    neglectT: T -⚬ Done,
    neglectNT: -[T] -⚬ Done,
    degenerify: GenericType[T] -⚬ DegenericType,
  )(using
    gen: VarGen[M, AbstractTypeLabel],
    M: Monad[M],
  ): M[One -⚬ (ConcreteType[T] |*| Val[TypedFun[A, B]] |*| ConcreteType[T])] = {
    println(s"reconstructTypes($f)")
    import ConcreteType.{apply1T, fixT, int, isPair, isRecCall, pair, recCall, string}
    import TypeEmitter.generify

    def reconstructTypes[A, B](f: Fun[A, B]): M[One -⚬ (ConcreteType[T] |*| Val[TypedFun[A, B]] |*| ConcreteType[T])] =
      TypeInference.reconstructTypes(f)(mergeInT, mergeIntoT, mergeT, splitT, makeT, outputT, neglectT, neglectNT, degenerify)

    def newAbstractType(v: AbstractTypeLabel): One -⚬ (TypeEmitter[T] |*| Val[Type] |*| TypeEmitter[T]) =
      TypeEmitter.newAbstractType(v)(mergeInT, mergeT, makeT, outputT, neglectT, neglectNT)

    def newAbstractTypeG(v: AbstractTypeLabel): One -⚬ (ConcreteType[T] |*| Val[Type] |*| ConcreteType[T]) =
      newAbstractType(v) > λ { case a |*| t |*| b =>
        generify(a) |*| t |*| generify(b)
      }

    def newTypeParam(v: AbstractTypeLabel): One -⚬ (Val[Type] |*| ConcreteType[T]) =
      demand[T] > λ { case nt |*| t =>
        outputT(constantVal(v) |*| t) |*| ConcreteType.typeParam(constantVal(v) |*| nt)
      }

    def merge: (ConcreteType[T] |*| ConcreteType[T]) -⚬ ConcreteType[T] =
      ConcreteType.merge(makeT, splitT, neglectT, neglectNT, mergeIntoT)

    def output: ConcreteType[T] -⚬ Val[Type] =
      degenerify > DegenericType.output

    f.value match {
      case FunT.IdFun() =>
        for {
          v <- gen.newVar
        } yield
          newAbstractTypeG(v)
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
            val x = output(merge(x1 |*| x2))
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
            val a = pair(a1 |*| a2)
            val b = pair(b1 |*| b2)
            val f = (f1 ** f2) :>> mapVal { case (f1, f2) => TypedFun.par(f1, f2) }
            a |*| f |*| b
          }
      case _: FunT.AssocLR[arr, a, b, c] =>
        for {
          a <- gen.newVar
          b <- gen.newVar
          c <- gen.newVar
        } yield {
          λ.* { one =>
            val a1 |*| ta |*| a2 = newAbstractTypeG(a)(one)
            val b1 |*| tb |*| b2 = newAbstractTypeG(b)(one)
            val c1 |*| tc |*| c2 = newAbstractTypeG(c)(one)
            val f = (ta ** tb ** tc) :>> mapVal { case ((a, b), c) => TypedFun.assocLR[a, b, c](a, b, c) }
            val in  = pair(pair(a1 |*| b1) |*| c1)
            val out = pair(a2 |*| pair(b2 |*| c2))
            in |*| f |*| out
          }
        }
      case _: FunT.AssocRL[arr, a, b, c] =>
        for {
          a <- gen.newVar
          b <- gen.newVar
          c <- gen.newVar
        } yield {
          λ.* { one =>
            val a1 |*| ta |*| a2 = newAbstractTypeG(a)(one)
            val b1 |*| tb |*| b2 = newAbstractTypeG(b)(one)
            val c1 |*| tc |*| c2 = newAbstractTypeG(c)(one)
            val f = (ta ** tb ** tc) :>> mapVal { case ((a, b), c) => TypedFun.assocRL[a, b, c](a, b, c) }
            val in  = pair(a1 |*| pair(b1 |*| c1))
            val out = pair(pair(a2 |*| b2) |*| c2)
            in |*| f |*| out
          }
        }
      case _: FunT.Swap[arr, a, b] =>
        for {
          a <- gen.newVar
          b <- gen.newVar
        } yield {
          λ.* { one =>
            val a1 |*| ta |*| a2 = newAbstractTypeG(a)(one)
            val b1 |*| tb |*| b2 = newAbstractTypeG(b)(one)
            val f = (ta ** tb) :>> mapVal { case (a, b) => TypedFun.swap[a, b](a, b) }
            val in  = pair(a1 |*| b1)
            val out = pair(b2 |*| a2)
            in |*| f |*| out
          }
        }
      case FunT.EitherF(f, g) =>
        for {
          tf <- reconstructTypes(f)
          tg <- reconstructTypes(g)
        } yield
          λ.* { one =>
            val a1 |*| f |*| b1 = tf(one)
            val a2 |*| g |*| b2 = tg(one)
            val a = ConcreteType.either(a1 |*| a2)
            val b = merge(b1 |*| b2)
            val h = (f ** g) :>> mapVal { case (f, g) => TypedFun.either(f, g) }
            a |*| h |*| b
          }
      case _: FunT.InjectL[arr, l, r] =>
        for {
          l <- gen.newVar
          r <- gen.newVar
        } yield
          λ.* { one =>
            val l1 |*| lt |*| l2 = newAbstractTypeG(l)(one)
            val        rt |*| r2 = newTypeParam(r)(one)
            val f = (lt ** rt) :>> mapVal { case (lt, rt) => TypedFun.injectL[l, r](lt, rt) }
            val b = ConcreteType.either(l2 |*| r2)
            (l1 |*| f |*| b)
          }
      case _: FunT.InjectR[arr, l, r] =>
        for {
          l <- gen.newVar
          r <- gen.newVar
        } yield
          λ.* { one =>
            val        lt |*| l2 = newTypeParam(l)(one)
            val r1 |*| rt |*| r2 = newAbstractTypeG(r)(one)
            val f = (lt ** rt) :>> mapVal { case (lt, rt) => TypedFun.injectR[l, r](lt, rt) }
            val b = ConcreteType.either(l2 |*| r2)
            (r1 |*| f |*| b)
          }
      case FunT.Distribute() =>
        throw NotImplementedError(s"at ${summon[SourcePos]}")
      case f: FunT.FixF[arr, f] =>
        M.pure(
          λ.* { one =>
            val fixF = fixT[T, f](f.f)(one)
            val fFixF = apply1T(f.f)(fixT[T, f](f.f)(one))
            val tf = constantVal(TypedFun.fix[f](TypeTag.toTypeFun(f.f).vmap(Left(_))))
            fFixF |*| tf |*| fixF
          }
        )
      case f: FunT.UnfixF[arr, f] =>
        M.pure(
          λ.* { one =>
            val fixF = fixT[T, f](f.f)(one)
            val fFixF = apply1T(f.f)(fixT[T, f](f.f)(one))
            val tf = constantVal(TypedFun.unfix[f](TypeTag.toTypeFun(f.f).vmap(Left(_))))
            fixF |*| tf |*| fFixF
          }
        )
      case FunT.Rec(f) =>
        for {
          tf <- reconstructTypes(f)
        } yield
          tf > λ { case aba |*| f |*| b1 =>
            isPair(aba) switch {
              case Right(ab |*| a1) =>
                isRecCall(ab) switch {
                  case Right(a0 |*| b0) =>
                    val a = merge(a0 |*| a1)
                    val b = merge(b0 |*| b1)
                    val h = f :>> mapVal { TypedFun.rec(_) }
                    a |*| h |*| b
                  case Left(ab) =>
                    (ab |*| f |*| a1 |*| b1) :>> crashNow(s"TODO (${summon[SourcePos]})")
                }
              case Left(aba) =>
                import scala.concurrent.duration._
                val d = (f ** output(aba) ** output(b1))
                  :>> printLine { case ((f, aba), b) =>
                    s"FUNCTION=${scala.util.Try(f.toString)}, IN-TYPE=$aba, OUT-TYPE=$b"
                  }
                d :>> fork :>> crashWhenDone(s"TODO (${summon[SourcePos]})")
                // (d |*| b1) :>> crashNow(s"TODO (${summon[SourcePos]})")
            }
          }
      case _: FunT.Recur[arr, a, b] =>
        for {
          va <- gen.newVar
          vb <- gen.newVar
        } yield
          λ.* { one =>
            val a1 |*| ta |*| a2 = one :>> newAbstractTypeG(va)
            val b1 |*| tb |*| b2 = one :>> newAbstractTypeG(vb)
            val tf = (ta ** tb) :>> mapVal { case (ta, tb) => TypedFun.recur[a, b](ta, tb) }
            val tIn = pair(recCall(a1 |*| b1) |*| a2)
            tIn |*| tf |*| b2
          }
      case FunT.ConstInt(n) =>
        throw NotImplementedError(s"at ${summon[SourcePos]}")
      case FunT.AddInts() =>
        throw NotImplementedError(s"at ${summon[SourcePos]}")
      case FunT.IntToString() =>
        M.pure(
          λ.* { one =>
            val a = done(one) :>> int[T]
            val b = done(one) :>> string[T]
            val tf = constantVal(TypedFun.intToString)
            a |*| tf |*| b
          }
        )
    }
  }
}
