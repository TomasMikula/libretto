package libretto.typology.toylang.typeinfer

import libretto.lambda.util.{Monad, SourcePos}
import libretto.lambda.util.Monad.syntax._
import libretto.scaletto.StarterKit._
import libretto.scaletto.StarterKit.Comonoid.comonoidOne
import libretto.typology.kinds.{●}
import libretto.typology.toylang.terms.{Fun, FunT, TypedFun}
import libretto.typology.toylang.types.{Fix, AbstractTypeLabel, Type, TypeFun, TypeTag}
import libretto.typology.util.State
import libretto.scaletto.StarterKit

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

  private type NonAbstractTypeF[X] = (
    Val[(Type, Type)] // type mismatch
    |+| Done // unit
    |+| Done // int
    |+| Done // string
    |+| (Val[TypeFun[●, ●]] |*| X) // apply1
    |+| Val[TypeFun[●, ●]] // fix
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
                        constantVal(Type.abstractType(v))
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

    def merge__[T](
      splitOutbound: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| TypeEmitter[T]),
      mergeIntoOutbound: (TypeEmitter[T] |*| ReboundType[T]) -⚬ TypeEmitter[T],
      mergeInT: (TypeEmitter[T] |*| T) -⚬ TypeEmitter[T],
      makeT: ReboundType[T] -⚬ T,
      mergeT: (T |*| T) -⚬ T,
    ): (ReboundType[T] |*| ReboundType[T]) -⚬ ReboundType[T] =
      rec { self =>
        λ { case a |*| b =>
          (unpack(a) |*| unpack(b))
            :>> TypeSkelet.mergeOp(
              splitOutbound,
              mergeIntoOutbound,
              TypeEmitter.pack,
              tapFlop_(self, mergeInT, makeT, mergeT),
              self,
              outputApprox,
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
    ): (ReboundType[T] |*| ReboundType[T]) -⚬ ReboundType[T] =
      rec { self =>
        merge__(
          TypeEmitter.split_(self, tapFlop_(self, mergeInT, makeT, mergeT), mergeT),
          mergeIntoOutbound,
          mergeInT,
          makeT,
          mergeT,
        )
      }

    def merge[T](
      mergeInT: (TypeEmitter[T] |*| T) -⚬ TypeEmitter[T],
      makeT: ReboundType[T] -⚬ T,
      mergeT: (T |*| T) -⚬ T,
    ): (ReboundType[T] |*| ReboundType[T]) -⚬ ReboundType[T] =
      rec { self =>
        merge_(
          TypeEmitter.mergeIn(mergeInT, makeT, mergeT),
          mergeInT,
          makeT,
          mergeT,
        )
      }

    def tapFlop_[T](
      merge: (ReboundType[T] |*| ReboundType[T]) -⚬ ReboundType[T],
      mergeInT: (TypeEmitter[T] |*| T) -⚬ TypeEmitter[T],
      makeT: ReboundType[T] -⚬ T,
      mergeT: (T |*| T) -⚬ T,
    ): ReboundType[T] -⚬ (ReboundType[T] |*| TypeEmitter[T]) = rec { self =>
      val splitX: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| TypeEmitter[T]) =
        TypeEmitter.split_(merge, self, mergeT)

      val mergeInXY: (TypeEmitter[T] |*| ReboundType[T]) -⚬ TypeEmitter[T] =
        TypeEmitter.mergeIn_[T](merge, mergeInT, self, makeT, mergeT)

      rec { self =>
        unpack > TypeSkelet.tapFlop(splitX, mergeInXY, self, mergeT) > par(pack, TypeEmitter.pack)
      }
    }

    def tapFlop[T](
      mergeInT: (TypeEmitter[T] |*| T) -⚬ TypeEmitter[T],
      makeT: ReboundType[T] -⚬ T,
      mergeT: (T |*| T) -⚬ T,
    ): ReboundType[T] -⚬ (ReboundType[T] |*| TypeEmitter[T]) =
      tapFlop_(
        merge(mergeInT, makeT, mergeT),
        mergeInT,
        makeT,
        mergeT,
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

    def outputApprox[T]: ReboundType[T] -⚬ Val[Type] =
      rec { self =>
        unpack > TypeSkelet.outputApprox(self)
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

    def fix[X]: Val[TypeFun[●, ●]] -⚬ NonAbstractTypeF[X] =
      injectL ∘ injectL ∘ injectL ∘ injectR

    def fixT[X, F[_]](F: TypeTag[F]): One -⚬ NonAbstractTypeF[X] =
      fix ∘ const(TypeTag.toTypeFun(F))

    def apply1[X]: (Val[TypeFun[●, ●]] |*| X) -⚬ NonAbstractTypeF[X] =
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
                                          case Right(fg) => NonAbstractType.mismatch(fg :>> mapVal { case (f, g) => (Type.fix(f), Type.fix(g)) })
                                        }
                                      case Left(b) =>
                                        NonAbstractType.mismatch(
                                          (f :>> mapVal { f => Type.fix(f) })
                                          ** output(outputYApprox)(injectL(injectL(injectL(injectL(b)))))
                                        )
                                    }
                                  case Left(a) =>
                                    b switch {
                                      case Right(g) => // `b` is fix
                                        NonAbstractType.mismatch(
                                          output(outputXApprox)(injectL(injectL(injectL(injectL(a)))))
                                          ** (g :>> mapVal { g => Type.fix(g) })
                                        )
                                      case Left(b) =>
                                        a switch {
                                          case Right(f |*| x) => // `a` is apply1
                                            (f |*| x |*| b) :>> crashNow(s"Not implemented (at ${summon[SourcePos]})")
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
                                                                        val ta = x :>> constVal(Type.unit)
                                                                        NonAbstractType.mismatch(ta ** tb)
                                                                    }
                                                                  case Left(ax) => // `a` is type mismatch
                                                                    val ta = ax :>> mapVal { case (t, u) => Type.typeMismatch(t, u) }
                                                                    b switch {
                                                                      case Right(y) => // `b` is unit
                                                                        val tb = y :>> constVal(Type.unit)
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
                        tf :>> mapVal { Type.fix(_) }
                      case Left(x) =>
                        x switch {
                          case Right(tf |*| a) => // apply1
                            (tf ** outputX(a)) :>> mapVal { case (f, a) =>
                              f(a)
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
                  case Right(f |*| x) => apply1(f.waitFor(d) |*| x)
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

    def fix[T]: Val[TypeFun[●, ●]] -⚬ ConcreteType[T] =
      NonAbstractType.fix > nonAbstractType

    def fixT[T, F[_]](F: TypeTag[F]): One -⚬ ConcreteType[T] =
      NonAbstractType.fixT(F) > nonAbstractType

    def apply1[T]: (Val[TypeFun[●, ●]] |*| ConcreteType[T]) -⚬ ConcreteType[T] =
      NonAbstractType.apply1 > nonAbstractType

    def apply1T[T, F[_]](F: TypeTag[F]): ConcreteType[T] -⚬ ConcreteType[T] =
      NonAbstractType.apply1T(F) > nonAbstractType

    def string[T]: Done -⚬ ConcreteType[T] =
      NonAbstractType.string > nonAbstractType

    def int[T]: Done -⚬ ConcreteType[T] =
      NonAbstractType.int > nonAbstractType

    def unit[T]: Done -⚬ ConcreteType[T]=
      NonAbstractType.unit > nonAbstractType

    def mismatch[T]: Val[(Type, Type)] -⚬ ConcreteType[T] =
      NonAbstractType.mismatch > nonAbstractType

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
    ): (ConcreteType[T] |*| ConcreteType[T]) -⚬ ConcreteType[T] =
      val abstractify = ConcreteType.abstractify(instantiate)
      par(abstractify, abstractify) > TypeEmitter.merge > TypeEmitter.generify
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

    def neglect: DegenericType -⚬ Done =
      ???

    def output: DegenericType -⚬ Val[Type] = rec { self =>
      unpack > either(
        NonAbstractType.output(self),
        mapVal { Type.abstractType },
      )
    }
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
    ): ((Label |*| RefinementRequestF[T, Y, X]) |*| (Label |*| RefinementRequestF[T, Y, X])) -⚬ X =
      λ { case (aLabel |*| aReq) |*| (bLabel |*| bReq) =>
        compareLabels(aLabel |*| bLabel) switch {
          case Left(label) => // labels are same => neither refines the other
            val x |*| resp = makeAbstractType[T, Y, X](aLabel)
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
              λ { case aLabel |*| aReq |*| bReq =>
                val y |*| resp = makeAbstractType[-[T], X, Y](aLabel)
                returning(
                  resp switch {
                    case Left(x) =>
                      val x1 |*| y1 = tapFlipXY(x)
                      returning(
                        x1,
                        RefinementRequest.completeWith(aReq |*| y1),
                      )
                    case Right(b) =>
                      b switch {
                        case Right(?(_)) =>
                          aReq :>> crashNow(s"TODO: eliminate ${summon[SourcePos]}")
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
                                    aReq :>> crashNow(s"TODO: eliminate ${summon[SourcePos]}")
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
      makeP: Y -⚬ P,
      makeQ: X -⚬ Q,
      tapFlipPQ: P -⚬ (P |*| Q),
      mergeP: (P |*| P) -⚬ P,
      makeX: TypeSkelet[P, Y, X] -⚬ X,
      makeY: TypeSkelet[Q, X, Y] -⚬ Y,
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
                mergeAbstractTypesOp(splitX, mergeInXY, tapFlopYX, makeX, makeY, makeP, makeQ, mergeP, tapFlipPQ, mergeInQP)(
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
      makeP: Y -⚬ P,
      makeQ: X -⚬ Q,
      mergeP: (P |*| P) -⚬ P,
      tapFlipPQ: P -⚬ (P |*| Q),
      mergeInQP: (Q |*| P) -⚬ Q,
    ): ((Label |*| RefinementRequestF[P, Y, X]) |*| (Label |*| RefinementRequestF[Q, X, Y])) -⚬ X =
      λ { case (aLabel |*| aReq) |*| (bLabel |*| bReq) =>
        compareLabels(aLabel |*| bLabel) switch {
          case Left(label) => // labels are same => neither refines the other
            val x |*| resp = makeAbstractType[P, Y, X](aLabel)
            returning(
              makeX(x),
              resp switch {
                case Left(y) =>
                  ???
                case Right(value) => ???
              },
            )
            // val req = (aReq |*| bReq) :>> RefinementRequest.mergeOpWith(splitX, mergeInXY, tapFlopYX, makeP, makeQ, tapFlipPQ)
            // makeX(abstractType(label |*| req))
          case Right(res) =>
            res switch {
              case Left(+(aLabel)) =>
                val x |*| resp = makeAbstractType[P, Y, X](aLabel)
                returning(
                  resp switch {
                    case Left(y) =>
                      val y1 |*| x1 = tapFlopYX(y)
                      returning(
                        x1,
                        RefinementRequest.completeWith(aReq |*| y1),
                      )
                    case Right(b) =>
                      b switch {
                        case Right(?(_)) =>
                          aReq :>> crashNow(s"TODO: eliminate ${summon[SourcePos]}")
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
                                    aReq :>> crashNow(s"TODO: eliminate ${summon[SourcePos]}")
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
                        x1,
                        RefinementRequest.completeWith(bReq |*| x2),
                      )
                    case Right(a) =>
                      a switch {
                        case Right(?(_)) =>
                          bReq :>> crashNow(s"TODO: eliminate ${summon[SourcePos]}")
                        case Left(aReq1) =>
                          val x |*| resp = makeAbstractType[P, Y, X](aLabel)
                          returning(
                            makeX(x),
                            resp switch {
                              case Left(y) =>
                                val y1 |*| x1 = tapFlopYX(y)
                                returning(
                                  RefinementRequest.completeWith(bReq |*| x1),
                                  injectL(y1) supplyTo aReq,
                                )
                              case Right(value) =>
                                value switch {
                                  case Right(?(_)) =>
                                    bReq :>> crashNow(s"TODO: eliminate ${summon[SourcePos]}")
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
                              req :>> crashNow(s"TODO: is this case ever used? (${summon[SourcePos]})")
                          }
                      }
                    case Right(?(_)) =>
                      req :>> crashNow(s"TODO: is this case ever used? (${summon[SourcePos]})")
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

    def outputApprox[T, Y, X](
      outputXApprox: X -⚬ Val[Type],
    ): TypeSkelet[T, Y, X] -⚬ Val[Type] =
      λ { _ switch {
        case Right(label |*| req) => // abstract type
          returning(
            label :>> mapVal(Type.abstractType),
            RefinementRequest.decline0(req),
          )
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

    def pair[T, Y]: (TypeEmitterF[T, Y] |*| TypeEmitterF[T, Y]) -⚬ TypeEmitterF[T, Y] =
      pack ∘ injectL ∘ injectR

    def either[T, Y]: (TypeEmitterF[T, Y] |*| TypeEmitterF[T, Y]) -⚬ TypeEmitterF[T, Y] =
      pack ∘ injectL ∘ injectL ∘ injectR

    def recCall[T, Y]: (TypeEmitterF[T, Y] |*| TypeEmitterF[T, Y]) -⚬ TypeEmitterF[T, Y] =
      pack ∘ injectL  ∘ injectL ∘ injectL ∘ injectR

    def fix[T, Y]: Val[TypeFun[●, ●]] -⚬ TypeEmitterF[T, Y] =
      pack ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

    def fixT[T, Y, F[_]](F: TypeTag[F]): One -⚬ TypeEmitterF[T, Y] =
      fix ∘ const(TypeTag.toTypeFun(F))

    def apply1[T, Y]: (Val[TypeFun[●, ●]] |*| TypeEmitterF[T, Y]) -⚬ TypeEmitterF[T, Y] =
      pack ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

    def apply1T[T, Y, F[_]](F: TypeTag[F]): TypeEmitterF[T, Y] -⚬ TypeEmitterF[T, Y] =
      λ { x =>
        apply1(constantVal(TypeTag.toTypeFun(F)) |*| x)
      }

    def string[T, Y]: Done -⚬ TypeEmitterF[T, Y] =
      pack ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

    def int[T, Y]: Done -⚬ TypeEmitterF[T, Y] =
      pack ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

    def unit[T, Y]: Done -⚬ TypeEmitterF[T, Y] =
      pack ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

    def mismatch[T, Y]: Val[(Type, Type)] -⚬ TypeEmitterF[T, Y] =
      pack ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL

    def outputApprox[T, Y]: TypeEmitterF[T, Y] -⚬ Val[Type] =
      rec { self =>
        unpack > TypeSkelet.outputApprox(self)
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
    ): One -⚬ (TypeEmitter[T] |*| Val[Type] |*| TypeEmitter[T]) =
      TypeSkelet.newAbstractType[T, ReboundType[T], TypeEmitter[T]](v)(
        ReboundType.merge(mergeInT, makeT, mergeT),
        ReboundType.output(outputT),
        ReboundType.tapFlop(mergeInT, makeT, mergeT),
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
    ): TypeEmitter[T] -⚬ (TypeEmitter[T] |*| TypeEmitter[T]) =
      rec { self =>
        val mergeInbound = ReboundType.merge__(self, mergeIn(mergeInT, makeT, mergeT), mergeInT, makeT, mergeT)
        split_(
          mergeInbound,
          ReboundType.tapFlop_(mergeInbound, mergeInT, makeT, mergeT),
          mergeT,
        )
      }

    def tapFlip[T](
      splitT: T -⚬ (T |*| T),
    ): TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]) = rec { self =>
      λ { case TypeEmitter(a) =>
        TypeSkelet.tapFlip(
          ReboundType.split(),
          self,
          ReboundType.mergeIn(),
          splitT,
        )
      }
    }

    def merge__[T](
      instantiate: ReboundType[T] -⚬ T,
      splitT: T -⚬ (T |*| T),
    ): (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ TypeEmitter[T] = rec { self =>
      λ { case TypeEmitter(a) |*| TypeEmitter(b) =>
        TypeSkelet.merge(
          self,
          splitY = ReboundType.split(),
          tapFlipXY = tapFlip(splitT),
          makeX = pack,
          makeY = ReboundType.pack,
          makeT = instantiate, //: Y -⚬ T,
          splitT = splitT,
          outputApprox,
        )(a |*| b)
      }
    }

    def mergeIn__[T](
      split: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| TypeEmitter[T]),
      mergeRebound: (ReboundType[T] |*| ReboundType[T]) -⚬ ReboundType[T],
      mergeInT: (TypeEmitter[T] |*| T) -⚬ TypeEmitter[T],
      tapFlop: ReboundType[T] -⚬ (ReboundType[T] |*| TypeEmitter[T]),
      yt: ReboundType[T] -⚬ T,
      mergeT: (T |*| T) -⚬ T,
    ): (TypeEmitter[T] |*| ReboundType[T]) -⚬ TypeEmitter[T] = rec { self =>
      λ { case a |*| b =>
        val a1: $[TypeSkelet[  T , ReboundType[T], TypeEmitter[T]]] = unpack(a)
        val b1: $[TypeSkelet[-[T], TypeEmitter[T], ReboundType[T]]] = ReboundType.unpack(b)
        (a1 |*| b1) :>> TypeSkelet.mergeIn(split, mergeRebound, self, mergeInT, tapFlop, yt, mergeT, pack, ReboundType.pack, outputApprox, ReboundType.outputApprox) :>> pack
      }
    }

    def mergeIn_[T](
      mergeInbound: (ReboundType[T] |*| ReboundType[T]) -⚬ ReboundType[T],
      mergeInT: (TypeEmitter[T] |*| T) -⚬ TypeEmitter[T],
      tapFlop: ReboundType[T] -⚬ (ReboundType[T] |*| TypeEmitter[T]),
      makeT: ReboundType[T] -⚬ T,
      mergeT: (T |*| T) -⚬ T,
    ): (TypeEmitter[T] |*| ReboundType[T]) -⚬ TypeEmitter[T] =
      mergeIn__[T](
        split_(mergeInbound, tapFlop, mergeT),
        mergeInbound,
        mergeInT,
        tapFlop,
        makeT,
        mergeT,
      )

    def mergeIn[T](
      mergeInT: (TypeEmitter[T] |*| T) -⚬ TypeEmitter[T],
      makeT: ReboundType[T] -⚬ T,
      mergeT: (T |*| T) -⚬ T,
    ): (TypeEmitter[T] |*| ReboundType[T]) -⚬ TypeEmitter[T] = rec { self =>
      val mergeInbound =
        ReboundType.merge_(
          self,
          mergeInT,
          makeT,
          mergeT,
        )

      mergeIn_[T](
        mergeInbound,
        mergeInT,
        ReboundType.tapFlop_(mergeInbound, mergeInT, makeT, mergeT),
        makeT,
        mergeT,
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

    def outputApprox[T]: TypeEmitter[T] -⚬ Val[Type] =
      rec { self =>
        unpack > TypeSkelet.outputApprox(self)
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

    def just: ReboundType[InboundType] -⚬ InboundType =
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
            (a |*| b) :>> TypeEmitter.mergeIn(self, just, merge)
        }
      }
    }

    def mergeTo: (TypeEmitter[InboundType] |*| InboundType) -⚬ TypeEmitter[InboundType] =
      mergeTo_(merge)

    def merge: (InboundType |*| InboundType) -⚬ InboundType =
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
                  (a |*| b) :>> ReboundType.merge_(TypeEmitter.mergeIn(mergeTo_(self), just, self), mergeTo_(self), just, self) :>> just
              }
          }
        }
      }

    def output: (Val[AbstractTypeLabel] |*| InboundType) -⚬ Val[Type] =
      rec { self =>
        λ { case lbl |*| t =>
          Maybe.toEither(unpack(t)) switch {
            case Left(?(_)) =>
              lbl :>> mapVal { Type.abstractType }
            case Right(t) =>
              (t :>> ReboundType.output(self))
                .waitFor(neglect(lbl))
          }
        }
      }
  }

  private def degenerify: GenericType[InboundType] -⚬ DegenericType =
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
    given VarGen[State[Int, *], AbstractTypeLabel] with {
      override def newVar: State[Int, AbstractTypeLabel] =
        State(n => (n+1, AbstractTypeLabel(n)))
    }

    reconstructTypes[InboundType, A, B, State[Int, *]](f)(
      InboundType.mergeTo,
      InboundType.merge,
      InboundType.just,
      InboundType.output,
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
  }

  def reconstructTypes[T, A, B, M[_]](f: Fun[A, B])(
    mergeInT: (TypeEmitter[T] |*| T) -⚬ TypeEmitter[T],
    mergeT: (T |*| T) -⚬ T,
    makeT: ReboundType[T] -⚬ T,
    outputT: (Val[AbstractTypeLabel] |*| T) -⚬ Val[Type],
    degenerify: GenericType[T] -⚬ DegenericType,
  )(using
    gen: VarGen[M, AbstractTypeLabel],
    M: Monad[M],
  ): M[One -⚬ (ConcreteType[T] |*| Val[TypedFun[A, B]] |*| ConcreteType[T])] = {
    import ConcreteType.{apply1T, fixT, int, merge, pair, recCall, string}
    import TypeEmitter.generify

    def reconstructTypes[A, B](f: Fun[A, B]): M[One -⚬ (ConcreteType[T] |*| Val[TypedFun[A, B]] |*| ConcreteType[T])] =
      TypeInference.reconstructTypes(f)(mergeInT, mergeT, makeT, outputT, degenerify)

    def newAbstractType(v: AbstractTypeLabel): One -⚬ (TypeEmitter[T] |*| Val[Type] |*| TypeEmitter[T]) =
      TypeEmitter.newAbstractType(v)(mergeInT, mergeT, makeT, outputT)

    def newAbstractTypeG(v: AbstractTypeLabel): One -⚬ (ConcreteType[T] |*| Val[Type] |*| ConcreteType[T]) =
      newAbstractType(v) > λ { case a |*| t |*| b =>
        generify(a) |*| t |*| generify(b)
      }

    def newTypeParam(v: AbstractTypeLabel): One -⚬ (Val[Type] |*| ConcreteType[T]) =
      demand[T] > λ { case nt |*| t =>
        outputT(constantVal(v) |*| t) |*| ConcreteType.typeParam(constantVal(v) |*| nt)
      }

    def output: ConcreteType[T] -⚬ Val[Type] =
      degenerify > DegenericType.output

    def expectPair: ConcreteType[T] -⚬ (ConcreteType[T] |*| ConcreteType[T]) =
      ???

    def expectRecCall: ConcreteType[T] -⚬ (ConcreteType[T] |*| ConcreteType[T]) =
      ???

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
            val tf = constantVal(TypedFun.fix(f.f))
            fFixF |*| tf |*| fixF
          }
        )
      case f: FunT.UnfixF[arr, f] =>
        M.pure(
          λ.* { one =>
            val fixF = fixT[T, f](f.f)(one)
            val fFixF = apply1T(f.f)(fixT[T, f](f.f)(one))
            val tf = constantVal(TypedFun.unfix(f.f))
            fixF |*| tf |*| fFixF
          }
        )
      case FunT.Rec(f) =>
        for {
          tf <- reconstructTypes(f)
        } yield
          tf > λ { case aba |*| f |*| b1 =>
            val ab |*| a1 = expectPair(aba)
            val a0 |*| b0 = expectRecCall(ab)
            val a = merge(a0 |*| a1)
            val b = merge(b0 |*| b1)
            val h = f :>> mapVal { TypedFun.rec(_) }
            a |*| h |*| b
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
