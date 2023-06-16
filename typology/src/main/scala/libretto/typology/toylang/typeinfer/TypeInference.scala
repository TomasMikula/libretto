
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
  private type ConcreteTypeF[T, X] = NonAbstractTypeF[T] |+| TypeParamF[T]

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

  /** Type param may be instantiated to types of "type" T. */
  private type TypeParamF[T] = Val[AbstractTypeLabel] |*| -[Maybe[T]]

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
    // def completeWith[T]: (RefinementRequest[T] |*| TypeEmitterG[T, TypeEmitter[T]]) -⚬ One =
    //   λ { case req |*| t => injectL(t) supplyTo req }

    def decline[T]: RefinementRequest[T] -⚬ (TypeEmitter[T] |+| -[T]) =
      λ { req =>
        req
          .contramap(injectR ∘ injectL)
          .unInvertWith(forevert > swap)
      }

    def decline0[T]: RefinementRequest[T] -⚬ One =
      λ { req =>
        req.contramap(injectR ∘ injectR) :>> unInvertOne
      }

    def merge[T](
      unify: (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ TypeEmitter[T],
      mergeT: (T |*| T) -⚬ T,
    ): (RefinementRequest[T] |*| RefinementRequest[T]) -⚬ RefinementRequest[T] =
      λ { case -(r1) |*| -(r2) =>
        (Rebound.dup(unify, mergeT) >>: (r1 |*| r2)).asInputInv
      }

    def dup[T](
      unify: (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ TypeEmitter[T],
      dup: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| TypeEmitter[T]),
      mergeT: (T |*| T) -⚬ T,
    ): RefinementRequest[T] -⚬ (RefinementRequest[T] |*| RefinementRequest[T]) =
      λ { case -(r) =>
        val r1 |*| r2 = Rebound.merge(unify, dup, mergeT) >>: r
        r1.asInputInv |*| r2.asInputInv
      }
  }

  object Rebound {
    def dup[T](
      unify: (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ TypeEmitter[T],
      mergeT: (T |*| T) -⚬ T,
    ): Rebound[T] -⚬ (Rebound[T] |*| Rebound[T]) =
      either(
        TypeEmitter.dup(unify, mergeT) > par(injectL, injectL),
        either(
          λ { yld => injectR(injectL(yld)) |*| injectR(injectR($.one)) },
          λ { case +(one) => injectR(injectR(one)) |*| injectR(injectR(one)) },
        )
        // Yield.dup(unify) > par(injectR, injectR),
      )

    def merge[T](
      unify: (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ TypeEmitter[T],
      dup: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| TypeEmitter[T]),
      mergeT: (T |*| T) -⚬ T,
    ): (Rebound[T] |*| Rebound[T]) -⚬ Rebound[T] =
      λ { case a |*| b =>
        a switch {
          case Left(refinedA) =>
            b switch {
              case Left(refinedB) =>
                injectL(unify(refinedA |*| refinedB))
              case Right(yieldB) =>
                yieldB switch {
                  case Left(yieldB) =>
                    val a1 |*| a2 = dup(refinedA)
                    injectL(a1) alsoElim (injectL(a2) supplyTo yieldB)
                  case Right(?(_)) =>
                    injectL(refinedA)
                }
            }
          case Right(yieldA) =>
            b switch {
              case Left(refinedB) =>
                yieldA switch {
                  case Left(yieldA) =>
                    val b1 |*| b2 = dup(refinedB)
                    injectL(b1) alsoElim (injectL(b2) supplyTo yieldA)
                  case Right(?(_)) =>
                    injectL(refinedB)
                }
              case Right(yieldB) =>
                injectR((yieldA |*| yieldB) :>> Yield.merge(dup, mergeT))
            }
        }
      }
  }

  object Yield {
    import TypeEmitter.given

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

    def merge[T](
      dup: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| TypeEmitter[T]),
      mergeT: (T |*| T) -⚬ T,
    ): (Yield[T] |*| Yield[T]) -⚬ Yield[T] =
      λ { case a |*| b =>
        a switch {
          case Left(-(a)) =>
            b switch {
              case Left(-(b)) =>
                producing { r =>
                  (a |*| b) :=
                    (injectL >>: r).asInput switch {
                      case Left(t) =>
                        val t1 |*| t2 = dup(t)
                        injectL(t1) |*| injectL(t2)
                      case Right(t) =>
                        val t1 |*| t2 = t.contramap(mergeT) :>> distributeInversion
                        injectR(t1) |*| injectR(t2)
                    }
                }
            }
        }
      }
  }

  object ReboundType {
    def pack[T]: ReboundTypeF[T, TypeEmitterF[T, ReboundType[T]]] -⚬ ReboundType[T] =
      dsl.pack[[X] =>> ReboundTypeF[T, TypeEmitterF[T, X]]]

    def unpack[T]: ReboundType[T] -⚬ ReboundTypeF[T, TypeEmitterF[T, ReboundType[T]]] =
      dsl.unpack
  }

  object TypeEmitter {

    private def pack[T]: TypeEmitterF[T, ReboundTypeF[T, TypeEmitter[T]]] -⚬ TypeEmitter[T] =
      dsl.pack[[X] =>> TypeEmitterF[T, ReboundTypeF[T, X]]]

    private def unpack[T]: TypeEmitter[T] -⚬ TypeEmitterF[T, ReboundTypeF[T, TypeEmitter[T]]] =
      dsl.unpack

    private def packF[T, Y]: TypeSkelet[T, Y, TypeEmitterF[T, Y]] -⚬ TypeEmitterF[T, Y] =
      dsl.pack

    // private def packF0[T]: TypeSkelet[T, ReboundType[T], TypeEmitterF[T, ReboundType[T]]] -⚬ TypeEmitterF[T, ReboundType[T]] =
    //   packF

    private def unpackF[T, Y]: TypeEmitterF[T, Y] -⚬ TypeSkelet[T, Y, TypeEmitterF[T, Y]] =
      dsl.unpack

    def unapply[T, Y](using SourcePos)(a: $[TypeEmitterF[T, Y]])(using LambdaContext): Some[$[TypeSkelet[T, Y, TypeEmitterF[T, Y]]]] =
      Some(unpackF(a))

    def abstractType[T, Y]: (Val[AbstractTypeLabel] |*| -[ReboundF[T, Y, TypeEmitterF[T, Y]]]) -⚬ TypeEmitterF[T, Y] =
      packF ∘ injectR

    def nonAbstractType[T, Y]: NonAbstractTypeF[TypeEmitterF[T, Y]] -⚬ TypeEmitterF[T, Y] =
      packF ∘ injectL

    def newAbstractType[T, Y](v: AbstractTypeLabel)(
      mergeT: (T |*| T) -⚬ T,
      outputT: T -⚬ Val[Type],
    ): One -⚬ (TypeEmitterF[T, Y] |*| Val[Type] |*| TypeEmitterF[T, Y]) =
      λ.* { _ =>
        producing { case tl |*| t |*| tr =>
          ((abstractType[T, Y] >>: tl) |*| (abstractType[T, Y] >>: tr)) match {
            case (lblL |*| recvL) |*| (lblR |*| recvR) =>
              returning(
                const(v) >>: lblL,
                const(v) >>: lblR,
                t := unifyRebounds(v)(mergeT, outputT)(recvL.asInput |*| recvR.asInput),
              )
          }
        }
      }

    def pair[T, Y]: (TypeEmitterF[T, Y] |*| TypeEmitterF[T, Y]) -⚬ TypeEmitterF[T, Y] =
      packF ∘ injectL ∘ injectR

    def expectPair[T]: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| TypeEmitter[T]) =
      throw NotImplementedError(s"at ${summon[SourcePos]}")

    def either[T, Y]: (TypeEmitterF[T, Y] |*| TypeEmitterF[T, Y]) -⚬ TypeEmitterF[T, Y] =
      packF ∘ injectL ∘ injectL ∘ injectR

    def recCall[T, Y]: (TypeEmitterF[T, Y] |*| TypeEmitterF[T, Y]) -⚬ TypeEmitterF[T, Y] =
      packF ∘ injectL  ∘ injectL ∘ injectL ∘ injectR

    def expectRecCall[T]: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| TypeEmitter[T]) =
      throw NotImplementedError(s"at ${summon[SourcePos]}")

    def fix[T, Y]: Val[TypeFun[●, ●]] -⚬ TypeEmitterF[T, Y] =
      packF ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

    def fixT[T, Y, F[_]](F: TypeTag[F]): One -⚬ TypeEmitterF[T, Y] =
      fix ∘ const(TypeTag.toTypeFun(F))

    def apply1[T, Y]: (Val[TypeFun[●, ●]] |*| TypeEmitterF[T, Y]) -⚬ TypeEmitterF[T, Y] =
      packF ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

    def apply1T[T, Y, F[_]](F: TypeTag[F]): TypeEmitterF[T, Y] -⚬ TypeEmitterF[T, Y] =
      λ { x =>
        apply1(constantVal(TypeTag.toTypeFun(F)) |*| x)
      }

    def string[T]: Done -⚬ TypeEmitterF[T, Y] =
      packF ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

    def int[T, Y]: Done -⚬ TypeEmitterF[T, Y] =
      packF ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

    def unit[T, Y]: Done -⚬ TypeEmitterF[T, Y] =
      packF ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

    def mismatch[T, Y]: Val[(Type, Type)] -⚬ TypeEmitterF[T, Y] =
      packF ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL

    def unify[T, Y](
      mergeT: (T |*| T) -⚬ T,
    ): (TypeEmitterF[T, Y] |*| TypeEmitterF[T, Y]) -⚬ TypeEmitterF[T, Y] = rec { self =>
      λ { case TypeEmitter(a) |*| TypeEmitter(b) =>
        a switch {
          case Right(aLabel |*| aReq) => // `a` is abstract type
            b switch {
              case Right(bLabel |*| bReq) => // `b` is abstract type
                compareLabels(aLabel |*| bLabel) switch {
                  case Left(label) => // labels are same => neither refines the other
                    val req = RefinementRequest.merge(self, mergeT)(aReq |*| bReq)
                    abstractType(label |*| req)
                  case Right(res) =>
                    res switch {
                      case Left(aLabel) =>
                        val a1 |*| a2 = dup(self, mergeT)(abstractType(aLabel |*| aReq))
                        a2 alsoElim RefinementRequest.completeWith(bReq |*| a1)
                      case Right(bLabel) =>
                        val b1 |*| b2 = dup(self, mergeT)(abstractType(bLabel |*| bReq))
                        b2 alsoElim RefinementRequest.completeWith(aReq |*| b1)
                    }
                }
              case Left(b) => // `b` is not abstract type
                val b1 |*| b2 = dup(self, mergeT)(nonAbstractType(b))
                b2
                  .alsoElim(RefinementRequest.completeWith(aReq |*| b1))
                  .waitFor(neglect(aLabel))
            }
          case Left(a) => // `a` is not abstract type
            b switch {
              case Right(bLabel |*| bReq) => // `b` is abstract type
                val a1 |*| a2 = dup(self, mergeT)(nonAbstractType(a))
                a2
                  .alsoElim(RefinementRequest.completeWith(bReq |*| a1))
                  .waitFor(neglect(bLabel))
              case Left(b) => // `b` is not abstract type
                unifyNonAbstract(self)(a |*| b)
            }
        }
      }
    }

    private def unifyNonAbstract[T](
      unify: (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ TypeEmitter[T],
    ): (NonAbstractType[T] |*| NonAbstractType[T]) -⚬ TypeEmitter[T] =
      λ { case a |*| b =>
        a switch {
          case Right(a1 |*| a2) => // `a` is a pair
            b switch {
              case Right(b1 |*| b2) => // `b` is a pair
                TypeEmitter.pair(unify(a1 |*| b1) |*| unify(a2 |*| b2))
              case Left(b) =>
                TypeEmitter.mismatch(
                  ((outputApprox(a1) ** outputApprox(a2)) :>> mapVal { case (a1, a2) => Type.pair(a1, a2) })
                  ** outputNonAbstractApprox(injectL(b))
                )
            }
          case Left(a) =>
            b switch {
              case Right(b1 |*| b2) => // `b` is a pair
                TypeEmitter.mismatch(
                  outputNonAbstractApprox(injectL(a))
                  ** ((outputApprox(b1) ** outputApprox(b2)) :>> mapVal { case (b1, b2) => Type.pair(b1, b2) })
                )
              case Left(b) =>
                a switch {
                  case Right(p |*| q) => // `a` is either
                    b switch {
                      case Right(r |*| s) => // `b` is either
                        TypeEmitter.either(unify(p |*| r) |*| unify (q |*| s))
                      case Left(b) =>
                        TypeEmitter.mismatch(
                          ((outputApprox(p) ** outputApprox(q)) :>> mapVal { case (p, q) => Type.sum(p, q) })
                          ** outputNonAbstractApprox(injectL(injectL(b)))
                        )
                    }
                  case Left(a) =>
                    b switch {
                      case Right(r |*| s) => // `b` is either
                        TypeEmitter.mismatch(
                          outputNonAbstractApprox(injectL(injectL(a)))
                          ** ((outputApprox(r) ** outputApprox(s)) :>> mapVal { case (r, s) => Type.sum(r, s) })
                        )
                      case Left(b) =>
                        a switch {
                          case Right(p |*| q) => // `a` is RecCall
                            b switch {
                              case Right(r |*| s) => // `b` is RecCall
                                TypeEmitter.recCall(unify(p |*| q) |*| unify(r |*| s))
                              case Left(b) =>
                                TypeEmitter.mismatch(
                                  ((outputApprox(p) ** outputApprox(q)) :>> mapVal { case (p, q) => Type.recCall(p, q) })
                                  ** outputNonAbstractApprox(injectL(injectL(injectL(b))))
                                )
                            }
                          case Left(a) =>
                            b switch {
                              case Right(r |*| s) => // `b` is RecCall
                                TypeEmitter.mismatch(
                                  outputNonAbstractApprox(injectL(injectL(injectL(a))))
                                  ** ((outputApprox(r) ** outputApprox(s)) :>> mapVal { case (r, s) => Type.recCall(r, s) })
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
                                          case Left(f)   => TypeEmitter.fix(f)
                                          case Right(fg) => TypeEmitter.mismatch(fg :>> mapVal { case (f, g) => (Type.fix(f), Type.fix(g)) })
                                        }
                                      case Left(b) =>
                                        TypeEmitter.mismatch(
                                          (f :>> mapVal { f => Type.fix(f) })
                                          ** outputNonAbstractApprox(injectL(injectL(injectL(injectL(b)))))
                                        )
                                    }
                                  case Left(a) =>
                                    b switch {
                                      case Right(g) => // `b` is fix
                                        TypeEmitter.mismatch(
                                          outputNonAbstractApprox(injectL(injectL(injectL(injectL(a)))))
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
                                                        TypeEmitter.string(join(x |*| y))
                                                      case Left(b) =>
                                                        TypeEmitter.mismatch(
                                                          (x :>> constVal(Type.string))
                                                          ** outputNonAbstractApprox(injectL(injectL(injectL(injectL(injectL(injectL(b)))))))
                                                        )
                                                    }
                                                  case Left(a) =>
                                                    b switch {
                                                      case Right(y) => // `b` is string
                                                        TypeEmitter.mismatch(
                                                          outputNonAbstractApprox(injectL(injectL(injectL(injectL(injectL(injectL(a)))))))
                                                          ** (y :>> constVal(Type.string))
                                                        )
                                                      case Left(b) =>
                                                        a switch {
                                                          case Right(x) => // `a` is int
                                                            b switch {
                                                              case Right(y) => // `b` is int
                                                                TypeEmitter.int(join(x |*| y))
                                                              case Left(b) =>
                                                                TypeEmitter.mismatch(
                                                                  (x :>> constVal(Type.int))
                                                                  ** outputNonAbstractApprox(injectL(injectL(injectL(injectL(injectL(injectL(injectL(b))))))))
                                                                )
                                                            }
                                                          case Left(a) =>
                                                            b switch {
                                                              case Right(y) => // `b` is int
                                                                TypeEmitter.mismatch(
                                                                  outputNonAbstractApprox(injectL(injectL(injectL(injectL(injectL(injectL(injectL(a))))))))
                                                                  ** (y :>> constVal(Type.int))
                                                                )
                                                              case Left(b) =>
                                                                a switch {
                                                                  case Right(x) => // `a` is unit
                                                                    b switch {
                                                                      case Right(y) => // `b` is unit
                                                                        TypeEmitter.unit(join(x |*| y))
                                                                      case Left(bx) => // `b` is type mismatch
                                                                        val tb = bx :>> mapVal { case (t, u) => Type.typeMismatch(t, u) }
                                                                        val ta = x :>> constVal(Type.unit)
                                                                        TypeEmitter.mismatch(ta ** tb)
                                                                    }
                                                                  case Left(ax) => // `a` is type mismatch
                                                                    val ta = ax :>> mapVal { case (t, u) => Type.typeMismatch(t, u) }
                                                                    b switch {
                                                                      case Right(y) => // `b` is unit
                                                                        val tb = y :>> constVal(Type.unit)
                                                                        TypeEmitter.mismatch(ta ** tb)
                                                                      case Left(bx) => // `b` is type mismatch
                                                                        val tb = bx :>> mapVal { case (t, u) => Type.typeMismatch(t, u) }
                                                                        TypeEmitter.mismatch(ta ** tb)
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

    def unifyRebounds[T, Y](v: AbstractTypeLabel)(
      mergeY: (Y |*| Y) -⚬ Y,
      outputY: Y -⚬ Val[Type],
      mergeT: (T |*| T) -⚬ T,
      outputT: T -⚬ Val[Type],
    ): (ReboundF[T, Y, TypeEmitterF[T, Y]] |*| ReboundF[T, Y, TypeEmitterF[T, Y]]) -⚬ Val[Type] =
      λ { case l |*| r =>
        l switch {
          case Left(refinedL) =>
            r switch {
              case Left(refinedR) =>
                outputY(mergeY(refinedL |*| refinedR))
              case Right(unrefinedR) =>
                unrefinedR switch {
                  case Left(unrefinedR) =>
                    (refinedL :>> tap(mergeT)) match
                      case refinedL |*| t =>
                        t.alsoElim(injectL(refinedL) supplyTo unrefinedR)
                  case Right(?(_)) =>
                    output(refinedL)
                }
            }
          case Right(unrefinedL) =>
            unrefinedL switch {
              case Left(unrefinedL) =>
                r switch {
                  case Left(refinedR) =>
                    (refinedR :>> tap(mergeT)) match
                      case refinedR |*| t =>
                        t.alsoElim(injectL(refinedR) supplyTo unrefinedL)
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
                    output(refinedR)
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

    def tap[T, Y](
      mergeT: (T |*| T) -⚬ T,
    ): TypeEmitterF[T, Y] -⚬ (TypeEmitterF[T, Y] |*| Val[Type]) =
      dup(unify(mergeT), mergeT) > snd(output)

    def output[T, Y]: TypeEmitterF[T, Y] -⚬ Val[Type] = rec { output =>
      unpackF > λ { _ switch {
        case Right(label |*| req) => // abstract type
          RefinementRequest.decline(req) switch {
            case Left(t) =>
              output(t)
                .waitFor(neglect(label))
            case Right(no) =>
              (label :>> mapVal { Type.abstractType(_) })
                .waitFor(no)
          }
        case Left(x) =>
          outputNonAbstract0(output)(x)
      }}
    }

    def outputApprox[T, Y]: TypeEmitterF[T, Y] -⚬ Val[Type] = rec { output =>
      unpackF > λ { _ switch {
        case Right(label |*| req) => // abstract type
          returning(
            label :>> mapVal(Type.abstractType),
            RefinementRequest.decline0(req),
          )
        case Left(x) =>
          outputNonAbstract0(outputApprox)(x)
      }}
    }

    def outputNonAbstractApprox[T, Y]: NonAbstractTypeF[TypeEmitterF[T, Y]] -⚬ Val[Type] =
      outputNonAbstract0(outputApprox)

    def outputNonAbstract0[T, Y](
      output: TypeEmitter[T] -⚬ Val[Type],
    ): NonAbstractTypeF[TypeEmitterF[T, Y]] -⚬ Val[Type] =
      λ { x =>
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

    def dup[T, Y](
      unify: (TypeEmitterF[T, Y] |*| TypeEmitterF[T, Y]) -⚬ TypeEmitterF[T, Y],
      mergeT: (T |*| T) -⚬ T,
    ): TypeEmitterF[T, Y] -⚬ (TypeEmitterF[T, Y] |*| TypeEmitterF[T, Y]) = rec { dup =>
      λ { case TypeEmitter(t) =>
        t switch {
          case Right(+(lbl) |*| req) => // abstract type
            val r1 |*| r2 = req :>> RefinementRequest.dup(unify, dup, mergeT)
            abstractType(lbl |*| r1) |*| abstractType(lbl |*| r2)
          case Left(t) =>
            t switch {
              case Right(r |*| s) => // pair
                val r1 |*| r2 = dup(r)
                val s1 |*| s2 = dup(s)
                pair(r1 |*| s1) |*| pair(r2 |*| s2)
              case Left(t) =>
                t switch {
                  case Right(r |*| s) => // either
                    val r1 |*| r2 = dup(r)
                    val s1 |*| s2 = dup(s)
                    either(r1 |*| s1) |*| either(r2 |*| s2)
                  case Left(t) =>
                    t switch {
                      case Right(r |*| s) => // RecCall
                        val r1 |*| r2 = dup(r)
                        val s1 |*| s2 = dup(s)
                        recCall(r1 |*| s1) |*| recCall(r2 |*| s2)
                      case Left(t) =>
                        t switch {
                          case Right(+(f)) => // fix
                            fix(f) |*| fix(f)
                          case Left(t) =>
                            t switch {
                              case Right(f |*| x) => // apply1
                                val f1 |*| f2 = dsl.dup(f)
                                val x1 |*| x2 = dup(x)
                                apply1(f1 |*| x1) |*| apply1(f2 |*| x2)
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
      }
    }

    def disengage[T]: TypeEmitter[T] -⚬ Done = rec { self =>
      λ { case TypeEmitter(t) =>
        t switch {
          case Right(lbl |*| req) =>
            returning(
              neglect(lbl),
              RefinementRequest.decline0(req),
            )
          case Left(t) => t switch {
            case Right(a |*| b) => join(self(a) |*| self(b))
            case Left(t) => t switch {
              case Right(a |*| b) => join(self(a) |*| self(b))
              case Left(t) => t switch {
                case Right(a |*| b) => join(self(a) |*| self(b))
                case Left(t) => t switch {
                  case Right(f) => neglect(f)
                  case Left(t) => t switch {
                    case Right(f |*| x) => join(neglect(f) |*| self(x))
                    case Left(t) => t switch {
                      case Right(t) => t
                      case Left(t) => t switch {
                        case Right(t) => t
                        case Left(t) => t switch {
                          case Right(t) => t
                          case Left(t) => neglect(t)
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

    given junctionTypeEmitter[T]: Junction.Positive[TypeEmitter[T]] with {
      override def awaitPosFst: (Done |*| TypeEmitter[T]) -⚬ TypeEmitter[T] = rec { self =>
        λ { case d |*| TypeEmitter(t) =>
          t switch {
            case Right(label |*| req) => abstractType((label waitFor d) |*| req)
            case Left(t) => t switch {
              case Right(a |*| b) => pair(self(d |*| a) |*| b)
              case Left(t) => t switch {
                case Right(a |*| b) => either(self(d |*| a) |*| b)
                case Left(t) => t switch {
                  case Right(a |*| b) => recCall(self(d |*| a) |*| b)
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
        }
      }
    }
  }

  import TypeEmitter.{output, unify}

  def inferTypes[A, B](f: Fun[A, B]): One -⚬ Val[TypedFun[A, B]] = {
    given VarGen[State[Int, *], AbstractTypeLabel] with {
      override def newVar: State[Int, AbstractTypeLabel] =
        State(n => (n+1, AbstractTypeLabel(n)))
    }

    reconstructTypes[One, A, B, State[Int, *]](f)
      .map { prg =>
        prg > λ { case a |*| f |*| b =>
          f
            .waitFor(TypeEmitter.disengage(a))
            .waitFor(TypeEmitter.disengage(b))
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
  ): M[One -⚬ (TypeEmitter[T] |*| Val[TypedFun[A, B]] |*| TypeEmitter[T])] = {
    def reconstructTypes[A, B](f: Fun[A, B]) =
      TypeInference.reconstructTypes(f)(mergeT, outputT)

    def newAbstractType(v: AbstractTypeLabel) =
      TypeEmitter.newAbstractType(v)(mergeT, outputT)

    val unify =
      TypeEmitter.unify(mergeT)

    f.value match {
      case FunT.IdFun() =>
        for {
          v <- gen.newVar
        } yield
          newAbstractType(v)
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
      case _: FunT.AssocLR[arr, a, b, c] =>
        for {
          a <- gen.newVar
          b <- gen.newVar
          c <- gen.newVar
        } yield {
          λ.* { one =>
            val a1 |*| ta |*| a2 = newAbstractType(a)(one)
            val b1 |*| tb |*| b2 = newAbstractType(b)(one)
            val c1 |*| tc |*| c2 = newAbstractType(c)(one)
            val f = (ta ** tb ** tc) :>> mapVal { case ((a, b), c) => TypedFun.assocLR[a, b, c](a, b, c) }
            val in  = TypeEmitter.pair(TypeEmitter.pair(a1 |*| b1) |*| c1)
            val out = TypeEmitter.pair(a2 |*| TypeEmitter.pair(b2 |*| c2))
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
            val a1 |*| ta |*| a2 = newAbstractType(a)(one)
            val b1 |*| tb |*| b2 = newAbstractType(b)(one)
            val c1 |*| tc |*| c2 = newAbstractType(c)(one)
            val f = (ta ** tb ** tc) :>> mapVal { case ((a, b), c) => TypedFun.assocRL[a, b, c](a, b, c) }
            val in  = TypeEmitter.pair(a1 |*| TypeEmitter.pair(b1 |*| c1))
            val out = TypeEmitter.pair(TypeEmitter.pair(a2 |*| b2) |*| c2)
            in |*| f |*| out
          }
        }
      case _: FunT.Swap[arr, a, b] =>
        for {
          a <- gen.newVar
          b <- gen.newVar
        } yield {
          λ.* { one =>
            val a1 |*| ta |*| a2 = newAbstractType(a)(one)
            val b1 |*| tb |*| b2 = newAbstractType(b)(one)
            val f = (ta ** tb) :>> mapVal { case (a, b) => TypedFun.swap[a, b](a, b) }
            val in  = TypeEmitter.pair(a1 |*| b1)
            val out = TypeEmitter.pair(b2 |*| a2)
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
            val l1 |*| lt |*| l2 = newAbstractType(l)(one)
            val r1 |*| rt |*| r2 = newAbstractType(r)(one)
            val f = (lt ** rt.waitFor(TypeEmitter.disengage(r1))) :>> mapVal { case (lt, rt) => TypedFun.injectL[l, r](lt, rt) }
            val b = TypeEmitter.either(l2 |*| r2)
            (l1 |*| f |*| b)
          }
      case _: FunT.InjectR[arr, l, r] =>
        for {
          l <- gen.newVar
          r <- gen.newVar
        } yield
          λ.* { one =>
            val l1 |*| lt |*| l2 = newAbstractType(l)(one)
            val r1 |*| rt |*| r2 = newAbstractType(r)(one)
            val f = (lt.waitFor(TypeEmitter.disengage(l1)) ** rt) :>> mapVal { case (lt, rt) => TypedFun.injectR[l, r](lt, rt) }
            val b = TypeEmitter.either(l2 |*| r2)
            (r1 |*| f |*| b)
          }
      case FunT.Distribute() =>
        throw NotImplementedError(s"at ${summon[SourcePos]}")
      case f: FunT.FixF[arr, f] =>
        M.pure(
          λ.* { one =>
            val fixF = TypeEmitter.fixT[T, f](f.f)(one)
            val fFixF = TypeEmitter.apply1T(f.f)(TypeEmitter.fixT[T, f](f.f)(one))
            val tf = constantVal(TypedFun.fix(f.f))
            fFixF |*| tf |*| fixF
          }
        )
      case f: FunT.UnfixF[arr, f] =>
        M.pure(
          λ.* { one =>
            val fixF = TypeEmitter.fixT[T, f](f.f)(one)
            val fFixF = TypeEmitter.apply1T(f.f)(TypeEmitter.fixT[T, f](f.f)(one))
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
            val a1 |*| ta |*| a2 = one :>> newAbstractType(va)
            val b1 |*| tb |*| b2 = one :>> newAbstractType(vb)
            val tf = (ta ** tb) :>> mapVal { case (ta, tb) => TypedFun.recur[a, b](ta, tb) }
            val tIn = TypeEmitter.pair(TypeEmitter.recCall(a1 |*| b1) |*| a2)
            tIn |*| tf |*| b2
          }
      case FunT.ConstInt(n) =>
        throw NotImplementedError(s"at ${summon[SourcePos]}")
      case FunT.AddInts() =>
        throw NotImplementedError(s"at ${summon[SourcePos]}")
      case FunT.IntToString() =>
        M.pure(
          λ.* { one =>
            val a = done(one) :>> TypeEmitter.int[T]
            val b = done(one) :>> TypeEmitter.string[T]
            val tf = constantVal(TypedFun.intToString)
            a |*| tf |*| b
          }
        )
    }
  }
}
