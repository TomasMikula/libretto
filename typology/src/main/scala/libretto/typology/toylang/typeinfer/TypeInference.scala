
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
    Val[(Type, Type)] // type mismatch
    |+| One // unit
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

  object RefinementRequest {
    def completeWith: (RefinementRequest |*| TypeEmitter) -⚬ One =
      λ { case req |*| t => injectL(t) supplyTo req }
  }

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

    def nonAbstractType: NonAbstractType -⚬ TypeEmitter =
      pack ∘ injectL

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

    def fix: Val[TypeFun[●, ●]] -⚬ TypeEmitter =
      pack ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

    def fixT[F[_]](F: TypeTag[F]): One -⚬ TypeEmitter =
      fix ∘ const(TypeTag.toTypeFun(F))

    def apply1: (Val[TypeFun[●, ●]] |*| TypeEmitter) -⚬ TypeEmitter =
      pack ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

    def apply1T[F[_]](F: TypeTag[F]): TypeEmitter -⚬ TypeEmitter =
      λ { x =>
        apply1(constantVal(TypeTag.toTypeFun(F)) |*| x)
      }

    def string: One -⚬ TypeEmitter =
      pack ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

    def int: One -⚬ TypeEmitter =
      pack ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

    def unit: One -⚬ TypeEmitter =
      pack ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

    def mismatch: Val[(Type, Type)] -⚬ TypeEmitter =
      pack ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL

    def unify: (TypeEmitter |*| TypeEmitter) -⚬ TypeEmitter = rec { self =>
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
                val b1 |*| b2 = dup(nonAbstractType(b))
                b2 alsoElim RefinementRequest.completeWith(aReq |*| b1)
                refineUnify(aReq |*| b) // TODO: consume aLabel
            }
          case Left(a) => // `a` is not abstract type
            b switch {
              case Right(bLabel |*| bReq) => // `b` is abstract type
                val a1 |*| a2 = dup(nonAbstractType(a))
                a2 alsoElim RefinementRequest.completeWith(bReq |*| a1) // TODO: consume bLabel
              case Left(b) => // `b` is not abstract type
                unifyNonAbstract(self)(a |*| b)
            }
        }
      }
    }

    def refineUnify: (RefinementRequest |*| NonAbstractType) -⚬ TypeEmitter =
      λ { case req |*| t =>
        val t1 |*| t2 = TypeEmitter.dup(TypeEmitter.nonAbstractType(t))
        t2 alsoElim RefinementRequest.completeWith(req |*| t1)
      }

    private def unifyNonAbstract(
      unify: (TypeEmitter |*| TypeEmitter) -⚬ TypeEmitter,
    ): (NonAbstractType |*| NonAbstractType) -⚬ TypeEmitter =
      λ { case a |*| b =>
        a switch {
          case Right(a1 |*| a2) => // `a` is a pair
            b switch {
              case Right(b1 |*| b2) => // `b` is a pair
                TypeEmitter.pair(unify(a1 |*| b1) |*| unify(a2 |*| b2))
              case Left(b) =>
                TypeEmitter.mismatch(
                  ((output(a1) ** output(a2)) :>> mapVal { case (a1, a2) => Type.pair(a1, a2) })
                  ** output(pack(injectL(injectL(b))))
                )
            }
          case Left(a) =>
            b switch {
              case Right(b1 |*| b2) => // `b` is a pair
                TypeEmitter.mismatch(
                  output(pack(injectL(injectL(a))))
                  ** ((output(b1) ** output(b2)) :>> mapVal { case (b1, b2) => Type.pair(b1, b2) })
                )
              case Left(b) =>
                a switch {
                  case Right(p |*| q) => // `a` is either
                    b switch {
                      case Right(r |*| s) => // `b` is either
                        TypeEmitter.either(unify(p |*| r) |*| unify (q |*| s))
                      case Left(b) =>
                        TypeEmitter.mismatch(
                          ((output(p) ** output(q)) :>> mapVal { case (p, q) => Type.sum(p, q) })
                          ** output(pack(injectL(injectL(injectL(b)))))
                        )
                    }
                  case Left(a) =>
                    b switch {
                      case Right(r |*| s) => // `b` is either
                        TypeEmitter.mismatch(
                          output(pack(injectL(injectL(injectL(a)))))
                          ** ((output(r) ** output(s)) :>> mapVal { case (r, s) => Type.sum(r, s) })
                        )
                      case Left(b) =>
                        a switch {
                          case Right(p |*| q) => // `a` is RecCall
                            b switch {
                              case Right(r |*| s) => // `b` is RecCall
                                TypeEmitter.recCall(unify(p |*| q) |*| unify(r |*| s))
                              case Left(b) =>
                                TypeEmitter.mismatch(
                                  ((output(p) ** output(q)) :>> mapVal { case (p, q) => Type.recCall(p, q) })
                                  ** output(pack(injectL(injectL(injectL(injectL(b))))))
                                )
                            }
                          case Left(a) =>
                            b switch {
                              case Right(r |*| s) => // `b` is RecCall
                                TypeEmitter.mismatch(
                                  output(pack(injectL(injectL(injectL(injectL(a))))))
                                  ** ((output(r) ** output(s)) :>> mapVal { case (r, s) => Type.recCall(r, s) })
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
                                          ** output(pack(injectL(injectL(injectL(injectL(injectL(b)))))))
                                        )
                                    }
                                  case Left(a) =>
                                    b switch {
                                      case Right(g) => // `b` is fix
                                        TypeEmitter.mismatch(
                                          output(pack(injectL(injectL(injectL(injectL(injectL(a)))))))
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
                                                  case Right(?(_)) => // `a` is string
                                                    b switch {
                                                      case Right(?(_)) => // `b` is string
                                                        constant(TypeEmitter.string)
                                                      case Left(b) =>
                                                        TypeEmitter.mismatch(
                                                          constantVal(Type.string)
                                                          ** output(pack(injectL(injectL(injectL(injectL(injectL(injectL(injectL(b)))))))))
                                                        )
                                                    }
                                                  case Left(a) =>
                                                    b switch {
                                                      case Right(?(_)) => // `b` is string
                                                        TypeEmitter.mismatch(
                                                          output(pack(injectL(injectL(injectL(injectL(injectL(injectL(injectL(a)))))))))
                                                          ** constantVal(Type.string)
                                                        )
                                                      case Left(b) =>
                                                        a switch {
                                                          case Right(?(_)) => // `a` is int
                                                            b switch {
                                                              case Right(?(_)) => // `b` is int
                                                                constant(TypeEmitter.int)
                                                              case Left(b) =>
                                                                TypeEmitter.mismatch(
                                                                  constantVal(Type.int) 
                                                                  ** output(pack(injectL(injectL(injectL(injectL(injectL(injectL(injectL(injectL(b))))))))))
                                                                )
                                                            }
                                                          case Left(a) =>
                                                            b switch {
                                                              case Right(?(_)) => // `b` is int
                                                                TypeEmitter.mismatch(
                                                                  output(pack(injectL(injectL(injectL(injectL(injectL(injectL(injectL(injectL(a))))))))))
                                                                  ** constantVal(Type.int)
                                                                )
                                                              case Left(b) =>
                                                                a switch {
                                                                  case Right(?(_)) => // `a` is unit
                                                                    b switch {
                                                                      case Right(?(_)) => // `b` is unit
                                                                        constant(TypeEmitter.unit)
                                                                      case Left(bx) => // `b` is type mismatch
                                                                        val tb = bx :>> mapVal { case (t, u) => Type.typeMismatch(t, u) }
                                                                        TypeEmitter.mismatch(constantVal(Type.unit) ** tb)
                                                                    }
                                                                  case Left(ax) => // `a` is type mismatch
                                                                    val ta = ax :>> mapVal { case (t, u) => Type.typeMismatch(t, u) }
                                                                    b switch {
                                                                      case Right(?(_)) => // `b` is unit
                                                                        TypeEmitter.mismatch(ta ** constantVal(Type.unit))
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
                                    case Left(x) =>
                                      x switch {
                                        case Right(one) => // unit
                                          one :>> const(Type.unit)
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
      }}
    }

    def dup: TypeEmitter -⚬ (TypeEmitter |*| TypeEmitter) = rec {dup =>
      λ { case TypeEmitter(t) =>
        t switch {
          case Right(at) => // abstract type
            at :>> crashNow(s"not implemented (at ${summon[SourcePos]})")
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
                                  case Right(?(_)) => // string
                                    constant(string) |*| constant(string)
                                  case Left(t) =>
                                    t switch {
                                      case Right(?(_)) => // int
                                        constant(int) |*| constant(int)
                                      case Left(t) =>
                                        t switch {
                                          case Right(?(_)) => // unit
                                            constant(unit) |*| constant(unit)
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
            val fixF = TypeEmitter.fixT(f.f)(one)
            val fFixF = TypeEmitter.apply1T(f.f)(TypeEmitter.fixT(f.f)(one))
            val tf = constantVal(TypedFun.fix(f.f))
            fFixF |*| tf |*| fixF
          }
        )
      case f: FunT.UnfixF[arr, f] =>
        M.pure(
          λ.* { one =>
            val fixF = TypeEmitter.fixT(f.f)(one)
            val fFixF = TypeEmitter.apply1T(f.f)(TypeEmitter.fixT(f.f)(one))
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
