package libretto.typology.toylang.typeinfer

import libretto.lambda.util.{Monad, SourcePos}
import libretto.lambda.util.Monad.syntax._
import libretto.scaletto.StarterKit._
import libretto.scaletto.StarterKit.Comonoid.comonoidOne
import libretto.typology.kinds.{●}
import libretto.typology.toylang.terms.{Fun, FunT, TypedFun}
import libretto.typology.toylang.types.{Fix, AbstractTypeLabel, Type, TypeFun, TypeTag}
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
                    ???
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
      outputT: T -⚬ Val[Type],
      flopMerge: Y -⚬ (X |*| Y),
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
                    val x |*| y = flopMerge(refinedL)
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
                    val x |*| y = flopMerge(refinedR)
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
                        outputT(t)
                      case Right(?(_)) =>
                        val --(t) = unrefinedL.contramap(injectR)
                        outputT(t)
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
                        outputT(t)
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

    // def dup[T](
    //   unify: (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ TypeEmitter[T],
    //   unifyT: (T |*| T) -⚬ T,
    // ): Yield[T] -⚬ (Yield[T] |*| Yield[T]) =
    //   λ { case -(out) =>
    //     producing { case in1 |*| in2 =>
    //       val x = in1.asInput
    //       val y = in2.asInput

    //       out :=
    //         x switch {
    //           case Left(x) =>
    //             y switch {
    //               case Left(y)  => injectL(unify(x |*| y))
    //               case Right(d) => injectL(x waitFor d) // TODO: impossible (both originate from the same origin, must be the same), make unrepresentable
    //             }
    //           case Right(d) =>
    //             y switch {
    //               case Left(y)  => injectL(y waitFor d) // TODO: impossible, make unrepresentable
    //               case Right(e) => injectR(join(d |*| e))
    //             }
    //         }
    //     }
    //   }

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
                ???
            }
          case Right(?(_)) =>
            ???
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
                ???
            }
          case Right(?(_)) =>
            ???
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

    def merge_[T](
      splitOutbound: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| TypeEmitter[T]),
    ): (ReboundType[T] |*| ReboundType[T]) -⚬ ReboundType[T] =
      rec { self =>
        λ { case a |*| b =>
          (unpack(a) |*| unpack(b))
            :>> TypeSkelet.merge(self, outputApprox, splitOutbound)
            :>> pack
        }
      }

    def merge[T](
      mergeT: (T |*| T) -⚬ T,
    ): (ReboundType[T] |*| ReboundType[T]) -⚬ ReboundType[T] =
      rec { self =>
        merge_(TypeEmitter.split_(self, tapFlop_(self, mergeT), mergeT))
      }

    def tapFlop_[T](
      merge: (ReboundType[T] |*| ReboundType[T]) -⚬ ReboundType[T],
      mergeT: (T |*| T) -⚬ T,
    ): ReboundType[T] -⚬ (ReboundType[T] |*| TypeEmitter[T]) = rec { self =>
      val splitX: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| TypeEmitter[T]) =
        TypeEmitter.split_(merge, self, mergeT)

      val mergeInXY: (TypeEmitter[T] |*| ReboundType[T]) -⚬ TypeEmitter[T] = ???

      rec { self =>
        unpack > TypeSkelet.tapFlop(splitX, mergeInXY, self, mergeT) > par(pack, TypeEmitter.pack)
      }
    }

    def outputApprox[T]: ReboundType[T] -⚬ Val[Type] =
      ???
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

    def unify[Y, X](
      mergeX: (X |*| X) -⚬ X,
      outputXApprox: X -⚬ Val[Type],
    ): (NonAbstractTypeF[X] |*| NonAbstractTypeF[X]) -⚬ NonAbstractTypeF[X] = {
      λ { case a |*| b =>
        a switch {
          case Right(a1 |*| a2) => // `a` is a pair
            b switch {
              case Right(b1 |*| b2) => // `b` is a pair
                NonAbstractType.pair(mergeX(a1 |*| b1) |*| mergeX(a2 |*| b2))
              case Left(b) =>
                NonAbstractType.mismatch(
                  ((outputXApprox(a1) ** outputXApprox(a2)) :>> mapVal { case (a1, a2) => Type.pair(a1, a2) })
                  ** output(outputXApprox)(injectL(b))
                )
            }
          case Left(a) =>
            b switch {
              case Right(b1 |*| b2) => // `b` is a pair
                NonAbstractType.mismatch(
                  output(outputXApprox)(injectL(a))
                  ** ((outputXApprox(b1) ** outputXApprox(b2)) :>> mapVal { case (b1, b2) => Type.pair(b1, b2) })
                )
              case Left(b) =>
                a switch {
                  case Right(p |*| q) => // `a` is either
                    b switch {
                      case Right(r |*| s) => // `b` is either
                        NonAbstractType.either(mergeX(p |*| r) |*| mergeX(q |*| s))
                      case Left(b) =>
                        NonAbstractType.mismatch(
                          ((outputXApprox(p) ** outputXApprox(q)) :>> mapVal { case (p, q) => Type.sum(p, q) })
                          ** output(outputXApprox)(injectL(injectL(b)))
                        )
                    }
                  case Left(a) =>
                    b switch {
                      case Right(r |*| s) => // `b` is either
                        NonAbstractType.mismatch(
                          output(outputXApprox)(injectL(injectL(a)))
                          ** ((outputXApprox(r) ** outputXApprox(s)) :>> mapVal { case (r, s) => Type.sum(r, s) })
                        )
                      case Left(b) =>
                        a switch {
                          case Right(p |*| q) => // `a` is RecCall
                            b switch {
                              case Right(r |*| s) => // `b` is RecCall
                                NonAbstractType.recCall(mergeX(p |*| q) |*| mergeX(r |*| s))
                              case Left(b) =>
                                NonAbstractType.mismatch(
                                  ((outputXApprox(p) ** outputXApprox(q)) :>> mapVal { case (p, q) => Type.recCall(p, q) })
                                  ** output(outputXApprox)(injectL(injectL(injectL(b))))
                                )
                            }
                          case Left(a) =>
                            b switch {
                              case Right(r |*| s) => // `b` is RecCall
                                NonAbstractType.mismatch(
                                  output(outputXApprox)(injectL(injectL(injectL(a))))
                                  ** ((outputXApprox(r) ** outputXApprox(s)) :>> mapVal { case (r, s) => Type.recCall(r, s) })
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
                                          ** output(outputXApprox)(injectL(injectL(injectL(injectL(b)))))
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

    def merge[T]: (ConcreteType[T] |*| ConcreteType[T]) -⚬ ConcreteType[T] =
      ???

    def output[T]: ConcreteType[T] -⚬ Val[Type] =
      ???
  }

  object DegenericType {
    def neglect: DegenericType -⚬ Done =
      ???
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

    def nonAbstractType[T, Y, X]: NonAbstractTypeF[X] -⚬ TypeSkelet[T, Y, X] =
      injectL

    def newAbstractType[T, Y, X](v: AbstractTypeLabel)(
      mergeT: (T |*| T) -⚬ T,
      outputT: T -⚬ Val[Type],
    ): One -⚬ (TypeSkelet[T, Y, X] |*| Val[Type] |*| TypeSkelet[T, Y, X]) =
      λ.* { _ =>
        producing { case tl |*| t |*| tr =>
          ((abstractType[T, Y, X] >>: tl) |*| (abstractType[T, Y, X] >>: tr)) match {
            case (lblL |*| recvL) |*| (lblR |*| recvR) =>
              returning(
                const(v) >>: lblL,
                const(v) >>: lblR,
                t := Rebound.unifyRebounds(v)(???, ???, mergeT, outputT, ???)(recvL.asInput |*| recvR.asInput),
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

    def merge[T, Y, X](
      mergeX: (X |*| X) -⚬ X,
      outputXApprox: X -⚬ Val[Type],
      splitY: Y -⚬ (Y |*| Y),
    ): (TypeSkelet[T, Y, X] |*| TypeSkelet[T, Y, X]) -⚬ TypeSkelet[T, Y, X] =
      λ { case a |*| b =>
        a switch {
          case Right(aLabel |*| aReq) => // `a` is abstract type
            b switch {
              case Right(bLabel |*| bReq) => // `b` is abstract type
                compareLabels(aLabel |*| bLabel) switch {
                  case Left(label) => // labels are same => neither refines the other
                    val req = RefinementRequest.merge(splitY)(aReq |*| bReq)
                    abstractType(label |*| req)
                  case Right(res) =>
                    res switch {
                      case Left(aLabel) =>
                        ???
                        // val req |*| y = RefinementRequest.splitListen(aReq)
                        // returning(
                        //   abstractType(aLabel |*| req),
                        //   RefinementRequest.completeWith(bReq |*| y),
                        // )
                      case Right(bLabel) =>
                        ???
                        // val req |*| y = RefinementRequest.splitListen(bReq)
                        // returning(
                        //   abstractType(bLabel |*| req),
                        //   RefinementRequest.completeWith(aReq |*| y),
                        // )
                    }
                }
              case Left(b) => // `b` is not abstract type
                val y |*| b1 = NonAbstractType.flopMerge[Y, X](b)
                returning(
                  nonAbstractType(b1),
                  RefinementRequest.completeWith(aReq |*| y),
                )
            }
          case Left(a) => // `a` is not abstract type
            b switch {
              case Right(bLabel |*| bReq) => // `b` is abstract type
                val y |*| a1 = NonAbstractType.flopMerge[Y, X](a)
                returning(
                  nonAbstractType(a1),
                  RefinementRequest.completeWith(bReq |*| y),
                )
              case Left(b) => // `b` is not abstract type
                nonAbstractType(NonAbstractType.unify(mergeX, outputXApprox)(a |*| b))
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

    def newAbstractType[T, Y](v: AbstractTypeLabel)(
      mergeT: (T |*| T) -⚬ T,
      outputT: T -⚬ Val[Type],
    ): One -⚬ (TypeEmitterF[T, Y] |*| Val[Type] |*| TypeEmitterF[T, Y]) =
      TypeSkelet.newAbstractType[T, Y, TypeEmitterF[T, Y]](v)(mergeT, outputT)
        > λ { case a |*| t |*| b => pack(a) |*| t |*| pack(b) }

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

    // def split[T, Y](
    //   mergeY: (Y |*| Y) -⚬ Y,
    //   flopMerge: Y -⚬ (TypeEmitterF[T, Y] |*| Y),
    //   mergeT: (T |*| T) -⚬ T,
    // ): TypeEmitterF[T, Y] -⚬ (TypeEmitterF[T, Y] |*| TypeEmitterF[T, Y]) = rec { self =>
    //   unpack > TypeSkelet.split(self, mergeY, flopMerge, mergeT) > par(pack, pack)
    // }

    def merge[T, Y](
      splitY: Y -⚬ (Y |*| Y),
    ): (TypeEmitterF[T, Y] |*| TypeEmitterF[T, Y]) -⚬ TypeEmitterF[T, Y] = rec { self =>
      λ { case TypeEmitter(a) |*| TypeEmitter(b) =>
        (a |*| b) :>> TypeSkelet.merge[T, Y, TypeEmitterF[T, Y]](self, outputApprox, splitY) :>> pack
      }
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

    def unapply[T, Y](using SourcePos)(a: $[TypeEmitterF[T, Y]])(using LambdaContext): Some[$[TypeSkelet[T, Y, TypeEmitterF[T, Y]]]] =
      Some(TypeEmitterF.unpack(a))

    def newAbstractType[T](v: AbstractTypeLabel)(
      mergeT: (T |*| T) -⚬ T,
      outputT: T -⚬ Val[Type],
    ): One -⚬ (TypeEmitter[T] |*| Val[Type] |*| TypeEmitter[T]) =
      TypeEmitterF.newAbstractType[T, ReboundType[T]](v)(mergeT, outputT)
        > λ { case a |*| t |*| b => pack1(a) |*| t |*| pack1(b) }

    // def abstractType[T, Y]: (Val[AbstractTypeLabel] |*| -[ReboundF[T, Y, TypeEmitterF[T, Y]]]) -⚬ TypeEmitterF[T, Y] =
    //   packF ∘ injectR

    // def nonAbstractType[T, Y]: NonAbstractTypeF[TypeEmitterF[T, Y]] -⚬ TypeEmitterF[T, Y] =
    //   packF ∘ injectL

    def expectPair[T]: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| TypeEmitter[T]) =
      throw NotImplementedError(s"at ${summon[SourcePos]}")

    def expectRecCall[T]: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| TypeEmitter[T]) =
      throw NotImplementedError(s"at ${summon[SourcePos]}")

    // def tap[T, Y](
    //   mergeT: (T |*| T) -⚬ T,
    // ): TypeEmitterF[T, Y] -⚬ (TypeEmitterF[T, Y] |*| Val[Type]) =
    //   dup(unify(mergeT), mergeT) > snd(output)

    // def output[T, Y, X](
    //   outputX: X -⚬ Val[Type],
    // ): TypeSkelet[T, Y, X] -⚬ Val[Type] =
    //   λ { _ switch {
    //     case Right(label |*| req) => // abstract type
    //       RefinementRequest.decline(req) switch {
    //         case Left(x) =>
    //           outputX(x)
    //             .waitFor(neglect(label))
    //         case Right(no) =>
    //           (label :>> mapVal { Type.abstractType(_) })
    //             .waitFor(no)
    //       }
    //     case Left(x) =>
    //       outputNonAbstract0(outputX)(x)
    //   }}

    // def outputNonAbstractApprox[T, Y]: NonAbstractTypeF[TypeEmitterF[T, Y]] -⚬ Val[Type] =
    //   outputNonAbstract0(outputApprox)

    def split_[T](
      mergeInbound: (ReboundType[T] |*| ReboundType[T]) -⚬ ReboundType[T],
      tapFlop: ReboundType[T] -⚬ (ReboundType[T] |*| TypeEmitter[T]),
      mergeT: (T |*| T) -⚬ T,
    ): TypeEmitter[T] -⚬ (TypeEmitter[T] |*| TypeEmitter[T]) = rec { self =>
      unpack > TypeSkelet.split(self, mergeInbound, tapFlop, mergeT) > par(pack, pack)
    }

    def split[T](
      mergeT: (T |*| T) -⚬ T,
    ): TypeEmitter[T] -⚬ (TypeEmitter[T] |*| TypeEmitter[T]) =
      rec { self =>
        split_(
          ReboundType.merge_(self),
          ReboundType.tapFlop_(ReboundType.merge_(self), mergeT),
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

    // given junctionTypeEmitter[T]: Junction.Positive[TypeEmitter[T]] with {
    //   override def awaitPosFst: (Done |*| TypeEmitter[T]) -⚬ TypeEmitter[T] = rec { self =>
    //     λ { case d |*| TypeEmitter(t) =>
    //       t switch {
    //         case Right(label |*| req) => abstractType((label waitFor d) |*| req)
    //         case Left(t) => t switch {
    //           case Right(a |*| b) => pair(self(d |*| a) |*| b)
    //           case Left(t) => t switch {
    //             case Right(a |*| b) => either(self(d |*| a) |*| b)
    //             case Left(t) => t switch {
    //               case Right(a |*| b) => recCall(self(d |*| a) |*| b)
    //               case Left(t) => t switch {
    //                 case Right(f) => fix(f waitFor d)
    //                 case Left(t) => t switch {
    //                   case Right(f |*| x) => apply1(f.waitFor(d) |*| x)
    //                   case Left(t) => t switch {
    //                     case Right(x) => string(join(d |*| x))
    //                     case Left(t) => t switch {
    //                       case Right(x) => int(join(d |*| x))
    //                       case Left(t) => t switch {
    //                         case Right(x) => unit(join(d |*| x))
    //                         case Left(e) => mismatch(e waitFor d)
    //                       }
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
  }

  type GenericType[T] = ConcreteType[T]

  type InboundType = Rec[[X] =>> Maybe[ReboundType[X]]]
  object InboundType {
    def pack: Maybe[ReboundType[InboundType]] -⚬ InboundType =
      dsl.pack[[X] =>> Maybe[ReboundType[X]]]

    def unpack: InboundType -⚬ Maybe[ReboundType[InboundType]] =
      dsl.unpack

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
                  (a |*| b) :>> ReboundType.merge(self) :>> Maybe.just :>> pack
              }
          }
        }
      }

    def output: InboundType -⚬ Val[Type] =
      ???
  }

  private def degenerify[T]: GenericType[InboundType] -⚬ DegenericType =
    ???

  def inferTypes[A, B](f: Fun[A, B]): One -⚬ Val[TypedFun[A, B]] = {
    given VarGen[State[Int, *], AbstractTypeLabel] with {
      override def newVar: State[Int, AbstractTypeLabel] =
        State(n => (n+1, AbstractTypeLabel(n)))
    }

    reconstructTypes[InboundType, A, B, State[Int, *]](f)(
      InboundType.merge,
      InboundType.output,
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
    mergeT: (T |*| T) -⚬ T,
    outputT: T -⚬ Val[Type],
  )(using
    gen: VarGen[M, AbstractTypeLabel],
    M: Monad[M],
  ): M[One -⚬ (ConcreteType[T] |*| Val[TypedFun[A, B]] |*| ConcreteType[T])] = {
    import ConcreteType.{apply1T, fixT, int, merge, output, pair, recCall, string}

    def reconstructTypes[A, B](f: Fun[A, B]): M[One -⚬ (ConcreteType[T] |*| Val[TypedFun[A, B]] |*| ConcreteType[T])] =
      TypeInference.reconstructTypes(f)(mergeT, outputT)

    def generify: TypeEmitter[T] -⚬ ConcreteType[T] =
      ???

    def newAbstractType(v: AbstractTypeLabel): One -⚬ (TypeEmitter[T] |*| Val[Type] |*| TypeEmitter[T]) =
      TypeEmitter.newAbstractType(v)(mergeT, outputT)

    def newAbstractTypeG(v: AbstractTypeLabel): One -⚬ (ConcreteType[T] |*| Val[Type] |*| ConcreteType[T]) =
      newAbstractType(v) > λ { case a |*| t |*| b =>
        generify(a) |*| t |*| generify(b)
      }

    def newTypeParam(v: AbstractTypeLabel): One -⚬ (Val[Type] |*| ConcreteType[T]) =
      ???

    def expectPair: ConcreteType[T] -⚬ (ConcreteType[T] |*| ConcreteType[T]) =
      ???

    def expectRecCall: ConcreteType[T] -⚬ (ConcreteType[T] |*| ConcreteType[T]) =
      ???

    // val mergeFlip: (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ ReboundType[T] =
    //   TypeEmitter.mergeFlip

    // val unify =
    //   TypeEmitter.merge(mergeT)

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
