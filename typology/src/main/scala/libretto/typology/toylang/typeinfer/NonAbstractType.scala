package libretto.typology.toylang.typeinfer

import libretto.lambda.{MappedMorphism, MonoidalObjectMap, SymmetricMonoidalCategory, UnhandledCase}
import libretto.lambda.util.{SourcePos, TypeEq}
import libretto.lambda.util.TypeEq.Refl
import libretto.scaletto.StarterKit._
import libretto.typology.inference.TypeOps
import libretto.typology.kinds.{Kind, ×, ○, ●}
import libretto.typology.toylang.terms.TypedFun
import libretto.typology.toylang.types.{Label, Routing, ScalaTypeParam, Type, TypeConstructor, TypeExpr, TypeFun, TypeTag}
import libretto.scaletto.StarterKit

type TypeFun[K, L] = libretto.typology.toylang.types.Type.Fun[ScalaTypeParam, K, L]
type TypeTagF = libretto.typology.toylang.types.Type.Fun[ScalaTypeParam, ●, ●]
type TypeTagPF = libretto.typology.toylang.types.Type.Fun[ScalaTypeParam, ● × ●, ●]

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
    |+| (Val[TypeConstructor.PFix[ScalaTypeParam, ●, ?]] |*| T)
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

  // def fixT[V, T, F[_]](F: TypeTag[F]): One -⚬ NonAbstractType[V, T] =
  //   fix ∘ const(TypeTag.toTypeFun(F))

  def pfix[V, T]: (Val[TypeConstructor.PFix[ScalaTypeParam, ●, ?]] |*| T) -⚬ NonAbstractType[V, T] =
    pack ∘ injectL ∘ injectL ∘ injectL ∘ injectR ∘ injectR

  // def apply1T[V, T, F[_]](
  //   F: TypeTag[F],
  //   split: T -⚬ (T |*| T),
  //   lift: NonAbstractType[V, T] -⚬ T,
  //   absType: Label => (One -⚬ T),
  // )(using Junction.Positive[T]): T -⚬ T =
  //   apply1(TypeTag.toTypeFun(F), split, lift, absType)

  // def apply1[V, T](
  //   f: TypeTagF,
  //   split: T -⚬ (T |*| T),
  //   lift: NonAbstractType[V, T] -⚬ T,
  //   absType: Label => (One -⚬ T),
  // )(using J: Junction.Positive[T]): T -⚬ T = {
  //   val ct = CompilationTarget[V, T](split, lift, absType)
  //   import ct.Map_●
  //   val g: ct.Arr[T, T] =
  //     import ct.given
  //     f.compile[ct.Arr, |*|, One, ct.as, T](
  //       Map_●,
  //       ct.compilePrimitive,
  //       [k, q] => (kq: ct.as[k, q]) => ct.split[k, q](kq),
  //     ).get(Map_●, Map_●)
  //   g > J.awaitPosFst
  // }

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
  )(using
    J: Junction.Positive[T], // TODO: eliminate (compile directly to `One -⚬ T`)
  ): One -⚬ T = {
    import libretto.typology.toylang.types.{TypeConstructor => TC}

    val ct = new CompilationTarget[V, T](inject, absType)
    import ct.{Map_○, Map_●}

    val g: ct.Arr[One, T] =
      import ct.given
      t.compile[ct.Arr, |*|, One, ct.as, One](
        Map_○,
        ct.compilePrimitive,
      ).get(Map_○, Map_●)

    g > J.awaitPosFst
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
                          pfix(f |*| g(x))
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
                        case Right(f |*| y) => // pfix
                          pfix(f |*| g(x |*| y))
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
                          val t1 |*| t2 = f(t)
                          pfix(g |*| t1) |*| pfix(g |*| t2)
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
                                                case Left(f)   => pfix(f |*| g(x |*| y))
                                                case Right(fh) => (fh |*| x |*| y) :>> crashNow(s"TODO type mismatch (at ${summon[SourcePos]})")
                                              }
                                          }
                                      }
                                    case Left(b) =>
                                      mismatch(
                                        (a switch {
                                          case Left(f)   => fix(f)
                                          case Right(fp) => pfix(fp)
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
                                          case Right(gy) => pfix(gy)
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
                          (pf ** outputElem(p)) :>> mapVal { case (pf, p) =>
                            Type.Fun.pfix(pf.vmap(Label.ScalaTParam(_))).apply(p)
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
                  case Right(f |*| x) => join(neglect(f) |*| closeElem(x))
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
                  case Right(f |*| x) => pfix(f.waitFor(d) |*| x)
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

  class CompiledPrimitives[V, T](
    lift: NonAbstractType[V, T] -⚬ T,
    absType: Label => (One -⚬ T),
  ):
    val unit: One -⚬ T =
      done > NonAbstractType.unit > lift
    val int: One -⚬ T =
      done > NonAbstractType.int > lift
    val string: One -⚬ T =
      done > NonAbstractType.string > lift
    val pair: (T |*| T) -⚬ T =
      NonAbstractType.pair > lift
    val sum: (T |*| T) -⚬ T =
      NonAbstractType.either > lift
    val recCall: (T |*| T) -⚬ T =
      NonAbstractType.recCall > lift
    def fix[X](f: TypeConstructor.Fix[ScalaTypeParam, X]): One -⚬ T =
      const(f) > NonAbstractType.fix > lift
    def pfix[X](f: TypeConstructor.PFix[ScalaTypeParam, ●, X]): T -⚬ T =
      λ { t =>
        (constantVal(f) |*| t) :>> NonAbstractType.pfix :>> lift
      }
    def abstractTypeName(name: ScalaTypeParam): One -⚬ T =
      absType(Label.ScalaTParam(name))

  class CompilationTarget[V, T](
    lift: NonAbstractType[V, T] -⚬ T,
    absType: Label => (One -⚬ T),
  ) {
    type Arr[K, L] = K -⚬ (Done |*| L)

    val cp = CompiledPrimitives(lift, absType)

    given category: SymmetricMonoidalCategory[Arr, |*|, One] =
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

    def doCompilePrimitive[k, l, q](
      fk: k as q,
      x: TypeConstructor[ScalaTypeParam, k, l],
    ): MappedMorphism[Arr, as, k, l] = {
      import TypeConstructor.{Pair as _, *}
      x match {
        case UnitType() =>
          MappedMorphism(Map_○, cp.unit > introFst(done), Map_●)
        case IntType() =>
          MappedMorphism(Map_○, cp.int > introFst(done), Map_●)
        case StringType() =>
          MappedMorphism(Map_○, cp.string > introFst(done), Map_●)
        case TypeConstructor.Pair() =>
          MappedMorphism(Pair(Map_●, Map_●), cp.pair > introFst(done), Map_●)
        case Sum() =>
          MappedMorphism(Pair(Map_●, Map_●), cp.sum > introFst(done), Map_●)
        case RecCall() =>
          MappedMorphism(Pair(Map_●, Map_●), cp.recCall > introFst(done), Map_●)
        case f @ Fix(_, _) =>
          MappedMorphism(Map_○, cp.fix(f) > introFst(done), Map_●)
        case p @ PFix(_, _) =>
          p.inKind match
            case Kind.Type =>
              summon[k =:= ●]
              MappedMorphism(Map_●, cp.pfix(p) > introFst(done), Map_●)
            case other =>
              UnhandledCase.raise(s"Unsupported recursive type parameterized by multiple types")
        case AbstractType(label) =>
          MappedMorphism(Map_○, cp.abstractTypeName(label) > introFst(done), Map_●)
        case TypeMismatch(a, b) =>
          UnhandledCase.raise(s"TypeMismatch($a, $b)")
        case ForbiddenSelfRef(v) =>
          UnhandledCase.raise(s"ForbiddenSelfReference($v)")
      }
    }

    val compilePrimitive: [k, l, q] => (k as q, TypeConstructor[ScalaTypeParam, k, l]) => MappedMorphism[Arr, as, k, l] =
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
    ): Arr[Q, Q |*| Q] =
      kq match {
        case Map_● =>
          splitT > introFst(done)
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
