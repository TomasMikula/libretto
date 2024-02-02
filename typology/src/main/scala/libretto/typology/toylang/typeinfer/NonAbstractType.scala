package libretto.typology.toylang.typeinfer

import libretto.lambda.{MappedMorphism, MonoidalObjectMap, SymmetricMonoidalCategory, UnhandledCase}
import libretto.lambda.util.{SourcePos, TypeEq}
import libretto.lambda.util.TypeEq.Refl
import libretto.scaletto.StarterKit._
import libretto.typology.inference.TypeOps
import libretto.typology.kinds.{Kinds, KindN, ×, ○, ●}
import libretto.typology.toylang.terms.TypedFun
import libretto.typology.toylang.types
import libretto.typology.toylang.types.{Label, Routing, ScalaTypeParam, Type, TypeConstructor, TypeExpr, TypeFun, TypeTag}
import libretto.scaletto.StarterKit

private[typeinfer] type KindMismatch[Types] = Types |*| Types
private[typeinfer] type TypesF[T, X] = KindMismatch[X] |+| (T |+| (X |*| X))
private[typeinfer] type Types[T] = Rec[TypesF[T, _]]

private[typeinfer] object Types {
  def pack[T]: TypesF[T, Types[T]] -⚬ Types[T] = dsl.pack[TypesF[T, _]]

  def singleType[T]: T -⚬ Types[T] = pack ∘ injectR ∘ injectL
  def prod[T]: (Types[T] |*| Types[T]) -⚬ Types[T] = pack ∘ injectR ∘ injectR
  def kindMismatch[T]: (Types[T] |*| Types[T]) -⚬ Types[T] = pack ∘ injectL

  def map[T, U](f: T -⚬ U): Types[T] -⚬ Types[U] =
    rec { self =>
      λ { ts =>
        unpack(ts) switch {
          case Left(x |*| y) =>
            kindMismatch(self(x) |*| self(y))
          case Right(ts) =>
            ts switch {
              case Left(t) => singleType(f(t))
              case Right(ts1 |*| ts2) => prod(self(ts1) |*| self(ts2))
            }
        }
      }
    }

  def splitMap[T, U, V](f: T -⚬ (U |*| V)): Types[T] -⚬ (Types[U] |*| Types[V]) =
    rec { self =>
      λ { ts =>
        unpack(ts) switch {
          case Left(mismatch) =>
            val x |*| y = mismatch
            val xu |*| xv = self(x)
            val yu |*| yv = self(y)
            kindMismatch(xu |*| yu) |*| kindMismatch(xv |*| yv)
          case Right(ts) =>
            ts switch {
              case Left(t) => f(t) :>> par(singleType, singleType)
              case Right(ts1 |*| ts2) => (self(ts1) |*| self(ts2)) > IXI > par(prod, prod)
            }
        }
      }
    }

  def mapWith[X, T, U](f: (X |*| T) -⚬ U)(using Cosemigroup[X]): (X |*| Types[T]) -⚬ Types[U] =
    rec { self =>
      λ { case +(x) |*| ts =>
        unpack(ts) switch {
          case Left(p |*| q) =>
            kindMismatch(self(x |*| p) |*| self(x |*| q))
          case Right(ts) =>
            ts switch {
              case Left(t) => singleType(f(x |*| t))
              case Right(ts1 |*| ts2) => prod(self(x |*| ts1) |*| self(x |*| ts2))
            }
        }
      }
    }

  def merge[T](f: (T |*| T) -⚬ T): (Types[T] |*| Types[T]) -⚬ Types[T] =
    rec { self =>
      λ { case ts |*| us =>
        unpack(ts) switch {
          case Right(ts) =>
            unpack(us) switch {
              case Right(us) =>
                ts switch {
                  case Left(t) =>
                    us switch {
                      case Left(u) =>
                        singleType(f(t |*| u))
                      case Right(us) =>
                        kindMismatch(singleType(t) |*| prod(us))
                    }
                  case Right(ts1 |*| ts2) =>
                    us switch {
                      case Left(u) =>
                        kindMismatch(prod(ts1 |*| ts2) |*| singleType(u))
                      case Right(us1 |*| us2) =>
                        prod(self(ts1 |*| us1) |*| self(ts2 |*| us2))
                    }
                }
              case Left(ux) =>
                kindMismatch(pack(injectR(ts)) |*| kindMismatch(ux))
            }
          case Left(tx) =>
            kindMismatch(kindMismatch(tx) |*| us)
        }
      }
    }

  def output[T](
    outputElem: T -⚬ Val[Type[Label]],
  ): Types[T] -⚬ Val[types.Types[Label]] =
    rec { self =>
      λ { ts =>
        unpack(ts) switch {
          case Right(ts) =>
            ts switch {
              case Left(t) =>
                outputElem(t) :>> mapVal { types.Types.SingleType(_) }
              case Right(ts |*| us) =>
                (self(ts) ** self(us)) :>> mapVal {
                  case (ts, us) => types.Types.Product(ts, us)
                }
            }
          case Left(x |*| y) =>
            (self(x) ** self(y)) :>> mapVal {
              case (x, y) => types.Types.KindMismatch(x, y)
            }
        }
      }
    }

  def close[T](
    closeElem: T -⚬ Done,
  ): Types[T] -⚬ Done =
    rec { self =>
      λ { ts =>
        unpack(ts) switch {
          case Right(ts) =>
            ts switch {
              case Left(t) => closeElem(t)
              case Right(t |*| u) => join(self(t) |*| self(u))
            }
          case Left(x |*| y) =>
            join(self(x) |*| self(y))
        }
      }
    }
}

private[typeinfer] type NonAbstractTypeF[V, T, X] = (
  (
    (X |*| X) // type mismatch
    |+| V     // forbidden self-reference
  )
  |+| Done // unit
  |+| Done // int
  |+| Done // string
  |+| ( // fix or pfix
    Val[TypeConstructor.Fix[ScalaTypeParam, ?]]

    // Parameterized fixed point.
    // The nesting of the types must correspond to the kinds of PFix type parameters.
    // Once Libretto has existentials, can use them to ensure well-kindedness statically.
    |+| (Val[TypeConstructor.PFix[ScalaTypeParam, ?, ?]] |*| Types[T])
  )
  |+| (T |*| T) // recCall
  |+| (T |*| T) // either
  |+| (T |*| T) // pair
)

private[typeinfer] type NonAbstractType[V, T] = Rec[NonAbstractTypeF[V, T, _]]

private[typeinfer] object NonAbstractType {
  private def pack[V, T]: NonAbstractTypeF[V, T, NonAbstractType[V, T]] -⚬ NonAbstractType[V, T] =
    dsl.pack

  private def unpack[V, T]: NonAbstractType[V, T] -⚬ NonAbstractTypeF[V, T, NonAbstractType[V, T]] =
    dsl.unpack

  def pair[V, T]: (T |*| T) -⚬ NonAbstractType[V, T] =
    pack ∘ injectR

  def either[V, T]: (T |*| T) -⚬ NonAbstractType[V, T] =
    pack ∘ injectL ∘ injectR

  def recCall[V, T]: (T |*| T) -⚬ NonAbstractType[V, T] =
    pack ∘ injectL ∘ injectL ∘ injectR

  def fix[V, T]: Val[TypeConstructor.Fix[ScalaTypeParam, ?]] -⚬ NonAbstractType[V, T] =
    pack ∘ injectL ∘ injectL ∘ injectL ∘ injectR ∘ injectL

  def pfixs[V, T]: (Val[TypeConstructor.PFix[ScalaTypeParam, ?, ?]] |*| Types[T]) -⚬ NonAbstractType[V, T] =
    pack ∘ injectL ∘ injectL ∘ injectL ∘ injectR ∘ injectR

  def pfix[V, T]: (Val[TypeConstructor.PFix[ScalaTypeParam, ●, ?]] |*| T) -⚬ NonAbstractType[V, T] =
    pfixs ∘ par(mapVal(p => p), Types.singleType[T])

  def string[V, T]: Done -⚬ NonAbstractType[V, T] =
    pack ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

  def int[V, T]: Done -⚬ NonAbstractType[V, T] =
    pack ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

  def unit[V, T]: Done -⚬ NonAbstractType[V, T] =
    pack ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

  def forbiddenSelfReference[V, T]: V -⚬ NonAbstractType[V, T] =
    pack ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

  def mismatch[V, T]: (NonAbstractType[V, T] |*| NonAbstractType[V, T]) -⚬ NonAbstractType[V, T] =
    pack ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL

  def lift[V, T](
    inject: NonAbstractType[V, T] -⚬ T,
    absType: Label => (One -⚬ T),
    t: Type[ScalaTypeParam],
  ): One -⚬ T = {
    import libretto.typology.toylang.types.{TypeConstructor => TC}

    val ct = new CompilationTarget[V, T](inject, absType)
    import ct.{Map_○, Map_●}

    t.compile[-⚬, |*|, One, ct.as, One](
      Map_○,
      ct.compilePrimitive,
    )(using coreLib.category)
      .get(Map_○, Map_●)
  }

  def isPair[V, T]: NonAbstractType[V, T] -⚬ (NonAbstractType[V, T] |+| (T |*| T)) =
    λ { t =>
      unpack(t) switch {
        case Right(r |*| s) => // pair
          injectR(r |*| s)
        case Left(t) =>
          injectL(pack(injectL(t)))
      }
    }

  def isRecCall[V, T]: NonAbstractType[V, T] -⚬ (NonAbstractType[V, T] |+| (T |*| T)) =
    λ { t =>
      unpack(t) switch {
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
                    pack(injectL(injectL(injectL(t))))
                  )
              }
          }
      }
    }

  def map[V, T, U](g: T -⚬ U): NonAbstractType[V, T] -⚬ NonAbstractType[V, U] = rec { self =>
    λ { t =>
      unpack(t) switch {
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
                    case Right(t) => // fix or pfix
                      t switch {
                        case Left(f) => // fix
                          fix(f)
                        case Right(f |*| x) => // pfix
                          pfixs(f |*| Types.map(g)(x))
                      }
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
                                case Left(e) =>
                                  e switch {
                                    case Left(x |*| y) =>
                                      mismatch(self(x) |*| self(y))
                                    case Right(v) =>
                                      forbiddenSelfReference(v)
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

  def mapWith[V, X, A, B](g: (X |*| A) -⚬ B)(using
    X: CloseableCosemigroup[X],
    V: Junction.Positive[V],
  ): (X |*| NonAbstractType[V, A]) -⚬ NonAbstractType[V, B] = rec { self =>
    λ { case +(x) |*| t =>
      unpack(t) switch {
        case Right(r |*| s) => // pair
          pair(g(x |*| r) |*| g(x |*| s))
        case Left(t) =>
          t switch {
            case Right(r |*| s) => // either
              either(g(x |*| r) |*| g(x |*| s))
            case Left(t) =>
              t switch {
                case Right(r |*| s) => // RecCall
                  recCall(g(x |*| r) |*| g(x |*| s))
                case Left(t) =>
                  t switch {
                    case Right(t) => // fix or pfix
                      t switch {
                        case Left(f) => // fix
                          fix(f waitFor X.close(x))
                        case Right(f |*| ts) => // pfix
                          pfixs(f |*| Types.mapWith(g)(x |*| ts))
                      }
                    case Left(t) =>
                      t switch {
                        case Right(d) => // string
                          string(d waitFor X.close(x))
                        case Left(t) =>
                          t switch {
                            case Right(d) => // int
                              int(d waitFor X.close(x))
                            case Left(t) =>
                              t switch {
                                case Right(d) => // unit
                                  unit(d waitFor X.close(x))
                                case Left(e) =>
                                  e switch {
                                    case Left(y |*| z) =>
                                      mismatch(self(x |*| y) |*| self(x |*| z))
                                    case Right(v) =>
                                      forbiddenSelfReference(v waitFor X.close(x))
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

  def splitMap[V, T, Y, Z](
    f: T -⚬ (Y |*| Z),
  )(using
    Cosemigroup[V],
  ): NonAbstractType[V, T] -⚬ (NonAbstractType[V, Y] |*| NonAbstractType[V, Z]) = rec { self =>
    λ { t =>
      unpack(t) switch {
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
                    case Right(t) => // fix or pfix
                      t switch {
                        case Left(+(g)) => // fix
                          fix(g) |*| fix(g)
                        case Right(+(g) |*| t) => // pfix
                          val t1 |*| t2 = Types.splitMap(f)(t)
                          pfixs(g |*| t1) |*| pfixs(g |*| t2)
                      }
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
                                case Left(e) =>
                                  e switch {
                                    case Right(+(v)) =>
                                      forbiddenSelfReference(v) |*| forbiddenSelfReference(v)
                                    case Left(x1 |*| x2) =>
                                      val y1 |*| z1 = self(x1)
                                      val y2 |*| z2 = self(x2)
                                      mismatch(y1 |*| y2) |*| mismatch(z1 |*| z2)
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

  def split[V, T](
    splitElem: T -⚬ (T |*| T),
  )(using
    Cosemigroup[V],
  ): NonAbstractType[V, T] -⚬ (NonAbstractType[V, T] |*| NonAbstractType[V, T]) =
    splitMap(splitElem)

  def merge[V, T](
    g: (T |*| T) -⚬ T,
  ): (NonAbstractType[V, T] |*| NonAbstractType[V, T]) -⚬ NonAbstractType[V, T] = {
    λ { case a |*| b =>
      unpack(a) switch {
        case Right(a1 |*| a2) => // `a` is a pair
          unpack(b) switch {
            case Right(b1 |*| b2) => // `b` is a pair
              pair(g(a1 |*| b1) |*| g(a2 |*| b2))
            case Left(b) =>
              mismatch(pair(a1 |*| a2) |*| pack(injectL(b)))
          }
        case Left(a) =>
          unpack(b) switch {
            case Right(b1 |*| b2) => // `b` is a pair
              mismatch(
                pack(injectL(a))
                |*| pair(b1 |*| b2)
              )
            case Left(b) =>
              a switch {
                case Right(p |*| q) => // `a` is either
                  b switch {
                    case Right(r |*| s) => // `b` is either
                      either(g(p |*| r) |*| g(q |*| s))
                    case Left(b) =>
                      mismatch(
                        either(p |*| q)
                        |*| pack(injectL(injectL(b)))
                      )
                  }
                case Left(a) =>
                  b switch {
                    case Right(r |*| s) => // `b` is either
                      mismatch(
                        pack(injectL(injectL(a)))
                        |*| either(r |*| s)
                      )
                    case Left(b) =>
                      a switch {
                        case Right(p |*| q) => // `a` is RecCall
                          b switch {
                            case Right(r |*| s) => // `b` is RecCall
                              recCall(g(p |*| r) |*| g(q |*| s))
                            case Left(b) =>
                              mismatch(
                                recCall(p |*| q)
                                |*| pack(injectL(injectL(injectL(b))))
                              )
                          }
                        case Left(a) =>
                          b switch {
                            case Right(r |*| s) => // `b` is RecCall
                              mismatch(
                                pack(injectL(injectL(injectL(a))))
                                |*| recCall(r |*| s)
                              )
                            case Left(b) =>
                              a switch {
                                case Right(a) => // `a` is fix or pfix
                                  b switch {
                                    case Right(b) => // `b` is fix or pfix
                                      a switch {
                                        case Left(f) =>
                                          b switch {
                                            case Left(g) =>
                                              ((f ** g) :>> mapVal { case (f, g) =>
                                                if (f == g) Left(f)
                                                else        Right((f, g))
                                              } :>> liftEither) switch {
                                                case Left(f) =>
                                                  fix(f)
                                                case Right(fg) =>
                                                  mismatch(fg :>> liftPair :>> par(fix, fix))
                                              }
                                            case Right(g |*| y) =>
                                              (f |*| g |*| y) :>> crashNow(s"TODO type mismatch (at ${summon[SourcePos]})")
                                          }
                                        case Right(f |*| x) =>
                                          b switch {
                                            case Left(g) =>
                                              (f |*| x |*| g) :>> crashNow(s"TODO type mismatch (at ${summon[SourcePos]})")
                                            case Right(h |*| y) =>
                                              ((f ** h) :>> mapVal { case (f, h) =>
                                                if (f == h) Left(f)
                                                else        Right((f, h))
                                              } :>> liftEither) switch {
                                                case Left(f)   => pfixs(f |*| Types.merge(g)(x |*| y))
                                                case Right(fh) => (fh |*| x |*| y) :>> crashNow(s"TODO type mismatch (at ${summon[SourcePos]})")
                                              }
                                          }
                                      }
                                    case Left(b) =>
                                      mismatch(
                                        (a switch {
                                          case Left(f)   => fix(f)
                                          case Right(fp) => pfixs(fp)
                                        })
                                        |*| pack(injectL(injectL(injectL(injectL(b)))))
                                      )
                                  }
                                case Left(a) =>
                                  b switch {
                                    case Right(b) => // `b` is fix or pfix
                                      mismatch(
                                        pack(injectL(injectL(injectL(injectL(a)))))
                                        |*| (b switch {
                                          case Left(g)   => fix(g)
                                          case Right(gy) => pfixs(gy)
                                        })
                                      )
                                    case Left(b) =>
                                      a switch {
                                        case Right(x) => // `a` is string
                                          b switch {
                                            case Right(y) => // `b` is string
                                              string(join(x |*| y))
                                            case Left(b) =>
                                              mismatch(
                                                string(x)
                                                |*| pack(injectL(injectL(injectL(injectL(injectL(b))))))
                                              )
                                          }
                                        case Left(a) =>
                                          b switch {
                                            case Right(y) => // `b` is string
                                              mismatch(
                                                pack(injectL(injectL(injectL(injectL(injectL(a))))))
                                                |*| string(y)
                                              )
                                            case Left(b) =>
                                              a switch {
                                                case Right(x) => // `a` is int
                                                  b switch {
                                                    case Right(y) => // `b` is int
                                                      int(join(x |*| y))
                                                    case Left(b) =>
                                                      mismatch(
                                                        int(x)
                                                        |*| pack(injectL(injectL(injectL(injectL(injectL(injectL(b)))))))
                                                      )
                                                  }
                                                case Left(a) =>
                                                  b switch {
                                                    case Right(y) => // `b` is int
                                                      mismatch(
                                                        pack(injectL(injectL(injectL(injectL(injectL(injectL(a)))))))
                                                        |*| int(y)
                                                      )
                                                    case Left(b) =>
                                                      a switch {
                                                        case Right(x) => // `a` is unit
                                                          b switch {
                                                            case Right(y) => // `b` is unit
                                                              unit(join(x |*| y))
                                                            case Left(b) => // `b` is an error
                                                              mismatch(
                                                                unit(x)
                                                                |*| pack(injectL(injectL(injectL(injectL(injectL(injectL(injectL(b))))))))
                                                              )
                                                          }
                                                        case Left(a) => // `a` is an error
                                                          b switch {
                                                            case Right(y) => // `b` is unit
                                                              mismatch(
                                                                pack(injectL(injectL(injectL(injectL(injectL(injectL(injectL(a))))))))
                                                                |*| unit(y)
                                                              )
                                                            case Left(b) => // `b` is an error
                                                              a switch {
                                                                case Right(ax) => // `a` is forbidden self-ref
                                                                  b switch {
                                                                    case Right(bx) => // `b` is forbidden self-ref
                                                                      mismatch(forbiddenSelfReference(ax) |*| forbiddenSelfReference(bx)) // TODO: support multiple error accumulation instead
                                                                    case Left(bx) => // `b` is a type mismatch
                                                                      mismatch(forbiddenSelfReference(ax) |*| mismatch(bx)) // TODO: support multiple error accumulation instead
                                                                  }
                                                                case Left(ax) => // `a` is a type mismatch
                                                                  b switch {
                                                                    case Right(bx) => // `b` is forbidden self-ref
                                                                      mismatch(mismatch(ax) |*| forbiddenSelfReference(bx)) // TODO: support multiple error accumulation instead
                                                                    case Left(bx) => // `b` is a type mismatch
                                                                      mismatch(mismatch(ax) |*| mismatch(bx)) // TODO: support multiple error accumulation instead
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

  def output[V, T](
    outputElem: T -⚬ Val[Type[Label]],
    selfRef: V -⚬ Val[Type[Label]],
  ): NonAbstractType[V, T] -⚬ Val[Type[Label]] = rec { self =>
    λ { x =>
      unpack(x) switch {
        case Right(x1 |*| x2) => // pair
          (outputElem(x1) ** outputElem(x2)) :>> mapVal { case (t1, t2) =>
            Type.pair(t1, t2)
          }
        case Left(x) =>
          x switch {
            case Right(a |*| b) => // either
              (outputElem(a) ** outputElem(b)) :>> mapVal { case (a, b) =>
                Type.pair(a, b)
              }
            case Left(x) =>
              x switch {
                case Right(a |*| b) => // recCall
                  (outputElem(a) ** outputElem(b)) :>> mapVal { case (a, b) =>
                    Type.recCall(a, b)
                  }
                case Left(x) =>
                  x switch {
                    case Right(x) => // fix or pfix
                      x switch {
                        case Left(f) =>
                          f :>> mapVal { f => Type.fix(f.vmap(Label.ScalaTParam(_))) }
                        case Right(pf |*| p) =>
                          (pf ** Types.output(outputElem)(p)) :>> mapVal { case (pf, p) =>
                            Type.Fun.pfixUnsafe(pf.vmap(Label.ScalaTParam(_)), p)
                          }
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
                                case Left(e) =>
                                  e switch {
                                    case Right(v) =>
                                      selfRef(v)
                                    case Left(x |*| y) => // mismatch
                                      (self(x) ** self(y)) :>> mapVal { case (t, u) => Type.typeMismatch(t, u) }
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

  def close[V, T](
    closeElem: T -⚬ Done,
    closeVar: V -⚬ Done,
  ): NonAbstractType[V, T] -⚬ Done = rec { self =>
    λ { t =>
      unpack(t) switch {
        case Right(a |*| b) => join(closeElem(a) |*| closeElem(b))
        case Left(t) => t switch {
          case Right(a |*| b) => join(closeElem(a) |*| closeElem(b))
          case Left(t) => t switch {
            case Right(a |*| b) => join(closeElem(a) |*| closeElem(b))
            case Left(t) => t switch {
              case Right(t) =>
                t switch {
                  case Left(f) => neglect(f)
                  case Right(f |*| x) => join(neglect(f) |*| Types.close(closeElem)(x))
                }
              case Left(t) => t switch {
                case Right(x) => x
                case Left(t) => t switch {
                  case Right(x) => x
                  case Left(t) => t switch {
                    case Right(x) => x
                    case Left(e) => e switch {
                      case Right(v) => closeVar(v)
                      case Left(x |*| y) => join(self(x) |*| self(y))
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

  def awaitPosFst[V, T](
    g: (Done |*| T) -⚬ T,
    h: (Done |*| V) -⚬ V,
  ): (Done |*| NonAbstractType[V, T]) -⚬ NonAbstractType[V, T] = rec { self =>
    λ { case d |*| t =>
      unpack(t) switch {
        case Right(a |*| b) => pair(g(d |*| a) |*| b)
        case Left(t) => t switch {
          case Right(a |*| b) => either(g(d |*| a) |*| b)
          case Left(t) => t switch {
            case Right(a |*| b) => recCall(g(d |*| a) |*| b)
            case Left(t) => t switch {
              case Right(t) =>
                t switch {
                  case Left(f) => fix(f waitFor d)
                  case Right(f |*| x) => pfixs(f.waitFor(d) |*| x)
                }
              case Left(t) => t switch {
                case Right(x) => string(join(d |*| x))
                case Left(t) => t switch {
                  case Right(x) => int(join(d |*| x))
                  case Left(t) => t switch {
                    case Right(x) => unit(join(d |*| x))
                    case Left(e) => e switch {
                      case Right(v) => forbiddenSelfReference(h(d |*| v))
                      case Left(x |*| y) => mismatch(self(d |*| x) |*| y)
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

  given junctionNonAbstractType[V, T](using
    T: Junction.Positive[T],
    V: Junction.Positive[V],
  ): Junction.Positive[NonAbstractType[V, T]] with {
    override def awaitPosFst: (Done |*| NonAbstractType[V, T]) -⚬ NonAbstractType[V, T] =
      NonAbstractType.awaitPosFst[V, T](T.awaitPosFst, V.awaitPosFst)
  }

  class CompilationTarget[V, T](
    lift: NonAbstractType[V, T] -⚬ T,
    absType: Label => (One -⚬ T),
  ) {
    def toTypes[P, Q](pq: P as Q)(using p: KindN[P]): Q -⚬ Types[T] =
      pq match
        case Map_○ =>
          KindN.cannotBeUnit(p)
        case Map_● =>
          Types.singleType[T]
        case π: Pair[p1, p2, q1, q2] =>
          val (p1, p2) = KindN.unpair(p: KindN[p1 × p2])
          par(
            toTypes(π.f1)(using p1),
            toTypes(π.f2)(using p2),
          ) > Types.prod

    def compilePFix[P, Q, X](
      pq: P as Q,
      f: TypeConstructor.PFix[ScalaTypeParam, P, X],
    )(using
      KindN[P],
    ): Q -⚬ T =
      λ { q =>
        (constantVal(f) |*| toTypes(pq)(q)) :>> NonAbstractType.pfixs :>> lift
      }

    def doCompilePrimitive[k, l, q](
      fk: k as q,
      x: TypeConstructor[ScalaTypeParam, k, l],
    ): MappedMorphism[-⚬, as, k, l] = {
      import TypeConstructor.{Pair as _, *}
      x match {
        case UnitType() =>
          MappedMorphism(Map_○, done > NonAbstractType.unit > lift, Map_●)
        case IntType() =>
          MappedMorphism(Map_○, done > NonAbstractType.int > lift, Map_●)
        case StringType() =>
          MappedMorphism(Map_○, done > NonAbstractType.string > lift, Map_●)
        case TypeConstructor.Pair() =>
          MappedMorphism(Pair(Map_●, Map_●), NonAbstractType.pair > lift, Map_●)
        case Sum() =>
          MappedMorphism(Pair(Map_●, Map_●), NonAbstractType.either > lift, Map_●)
        case RecCall() =>
          MappedMorphism(Pair(Map_●, Map_●), NonAbstractType.recCall > lift, Map_●)
        case f @ Fix(_, _) =>
          MappedMorphism(Map_○, const(f) > NonAbstractType.fix > lift, Map_●)
        case p @ PFix(_, _) =>
          import p.g.inKind1
          MappedMorphism(fk, compilePFix(fk, p), Map_●)
        case AbstractType(label) =>
          MappedMorphism(Map_○, absType(Label.ScalaTParam(label)), Map_●)
        case TypeMismatch(a, b) =>
          UnhandledCase.raise(s"TypeMismatch($a, $b)")
        case ForbiddenSelfRef(v) =>
          UnhandledCase.raise(s"ForbiddenSelfReference($v)")
      }
    }

    val compilePrimitive: [k, l, q] => (
      k as q,
      TypeConstructor[ScalaTypeParam, k, l],
    ) => MappedMorphism[-⚬, as, k, l] =
      [k, l, q] => (
        fk: k as q,
        x: TypeConstructor[ScalaTypeParam, k, l],
      ) =>
        doCompilePrimitive[k, l, q](fk, x)

    sealed trait as[K, Q]

    case object Map_○ extends as[○, One]
    case object Map_● extends as[●, T]
    case class Pair[K1, K2, Q1, Q2](
      f1: K1 as Q1,
      f2: K2 as Q2,
    ) extends as[K1 × K2, Q1 |*| Q2]

    def split[K, Q](splitT: T -⚬ (T |*| T))(
      kq: K as Q,
    ): Q -⚬ (Q |*| Q) =
      kq match {
        case Map_● =>
          splitT
        case other =>
          UnhandledCase.raise(s"split($other)")
      }

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

  given TypeOps[NonAbstractType[Val[Label], _], Type[Label], Label] with {
    override def map[A, B](f: A -⚬ B): NonAbstractType[Val[Label], A] -⚬ NonAbstractType[Val[Label], B] =
      NonAbstractType.map(f)

    override def mapWith[X, A, B](
      f: (X |*| A) -⚬ B,
    )(using CloseableCosemigroup[X]): (X |*| NonAbstractType[Val[Label], A]) -⚬ NonAbstractType[Val[Label], B] =
      NonAbstractType.mapWith(f)

    override def merge[A](
      f: (A |*| A) -⚬ A,
    ): (NonAbstractType[Val[Label], A] |*| NonAbstractType[Val[Label], A]) -⚬ NonAbstractType[Val[Label], A] =
      NonAbstractType.merge(f)

    override def split[A](f: A -⚬ (A |*| A)): NonAbstractType[Val[Label], A] -⚬ (NonAbstractType[Val[Label], A] |*| NonAbstractType[Val[Label], A]) =
      NonAbstractType.split(f)

    override def output[A](f: A -⚬ Val[Type[Label]]): NonAbstractType[Val[Label], A] -⚬ Val[Type[Label]] =
      NonAbstractType.output(f, mapVal(Type.forbiddenSelfReference(_)))

    override def close[A](f: A -⚬ Done): NonAbstractType[Val[Label], A] -⚬ Done =
      NonAbstractType.close(f, neglect)

    override def forbiddenSelfReference[A]: Val[Label] -⚬ NonAbstractType[Val[Label], A] =
      NonAbstractType.forbiddenSelfReference

    override def awaitPosFst[A](f: (Done |*| A) -⚬ A): (Done |*| NonAbstractType[Val[Label], A]) -⚬ NonAbstractType[Val[Label], A] =
      NonAbstractType.awaitPosFst(f, summon[Junction.Positive[Val[Label]]].awaitPosFst)
  }
}
