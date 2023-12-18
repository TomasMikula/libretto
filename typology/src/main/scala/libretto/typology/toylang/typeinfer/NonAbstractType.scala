package libretto.typology.toylang.typeinfer

import libretto.lambda.{MonoidalObjectMap, SymmetricMonoidalCategory}
import libretto.lambda.util.{SourcePos, TypeEq}
import libretto.lambda.util.TypeEq.Refl
import libretto.scaletto.StarterKit._
import libretto.typology.inference.TypeOps
import libretto.typology.kinds.{×, ○, ●}
import libretto.typology.toylang.terms.TypedFun
import libretto.typology.toylang.terms.TypedFun.Type
import libretto.typology.toylang.types.{Label, ScalaTypeParam, TypeAlgebra, TypeFun, TypeTag}
import libretto.scaletto.StarterKit
import libretto.lambda.UnhandledCase

type TypeFun[K, L] = libretto.typology.toylang.types.TypeFun[ScalaTypeParam, K, L]
type TypeTagF = libretto.typology.toylang.types.TypeFun[ScalaTypeParam, ●, ●]
type TypeTagPF = libretto.typology.toylang.types.TypeFun[ScalaTypeParam, ● × ●, ●]

private[typeinfer] type NonAbstractTypeF[X, T] = (
  (T |*| T) // type mismatch
  |+| Done // unit
  |+| Done // int
  |+| Done // string
  |+| (Val[TypeTagF] |+| (Val[TypeTagPF] |*| X)) // fix or pfix
  |+| (X |*| X) // recCall
  |+| (X |*| X) // either
  |+| (X |*| X) // pair
)

private[typeinfer] type NonAbstractType[X] = Rec[NonAbstractTypeF[X, _]]

private[typeinfer] object NonAbstractType {
  private def pack[X]: NonAbstractTypeF[X, NonAbstractType[X]] -⚬ NonAbstractType[X] =
    dsl.pack

  private def unpack[X]: NonAbstractType[X] -⚬ NonAbstractTypeF[X, NonAbstractType[X]] =
    dsl.unpack

  def pair[X]: (X |*| X) -⚬ NonAbstractType[X] =
    pack ∘ injectR

  def either[X]: (X |*| X) -⚬ NonAbstractType[X] =
    pack ∘ injectL ∘ injectR

  def recCall[X]: (X |*| X) -⚬ NonAbstractType[X] =
    pack ∘ injectL ∘ injectL ∘ injectR

  def fix[X]: Val[TypeTagF] -⚬ NonAbstractType[X] =
    pack ∘ injectL ∘ injectL ∘ injectL ∘ injectR ∘ injectL

  def fixT[X, F[_]](F: TypeTag[F]): One -⚬ NonAbstractType[X] =
    fix ∘ const(TypeTag.toTypeFun(F))

  def pfix[X]: (Val[TypeTagPF] |*| X) -⚬ NonAbstractType[X] =
    pack ∘ injectL ∘ injectL ∘ injectL ∘ injectR ∘ injectR

  def apply1T[X, F[_]](
    F: TypeTag[F],
    split: X -⚬ (X |*| X),
    lift: NonAbstractType[X] -⚬ X,
    absType: Label => (One -⚬ X),
  )(using Junction.Positive[X]): X -⚬ X =
    apply1(TypeTag.toTypeFun(F), split, lift, absType)

  def apply1[X](
    f: TypeTagF,
    split: X -⚬ (X |*| X),
    lift: NonAbstractType[X] -⚬ X,
    absType: Label => (One -⚬ X),
  )(using J: Junction.Positive[X]): X -⚬ X = {
    val ct = compilationTarget[X](split, lift, absType)
    import ct.Map_●
    val g: ct.Arr[X, X] =
      f.compile[ct.Arr, ct.as, X](
        ct.typeAlgebra,
        Map_●,
        Map_●,
        [k, q] => (kq: ct.as[k, q]) => ct.split[k, q](kq),
      ).get(Map_●, Map_●)
    g > J.awaitPosFst
  }

  def string[X]: Done -⚬ NonAbstractType[X] =
    pack ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

  def int[X]: Done -⚬ NonAbstractType[X] =
    pack ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

  def unit[X]: Done -⚬ NonAbstractType[X] =
    pack ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

  def mismatch[X]: (NonAbstractType[X] |*| NonAbstractType[X]) -⚬ NonAbstractType[X] =
    pack ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL

  def isPair[X]: NonAbstractType[X] -⚬ (NonAbstractType[X] |+| (X |*| X)) =
    λ { t =>
      unpack(t) switch {
        case Right(r |*| s) => // pair
          injectR(r |*| s)
        case Left(t) =>
          injectL(pack(injectL(t)))
      }
    }

  def isRecCall[X]: NonAbstractType[X] -⚬ (NonAbstractType[X] |+| (X |*| X)) =
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

  def map[X, Q](g: X -⚬ Q): NonAbstractType[X] -⚬ NonAbstractType[Q] = rec { self =>
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
                                case Left(x |*| y) =>
                                  mismatch(self(x) |*| self(y))
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
  ): NonAbstractType[X] -⚬ (NonAbstractType[Y] |*| NonAbstractType[Z]) = rec { self =>
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

  def split[X](
    splitX: X -⚬ (X |*| X),
  ): NonAbstractType[X] -⚬ (NonAbstractType[X] |*| NonAbstractType[X]) =
    splitMap(splitX)

  def merge[X](
    g: (X |*| X) -⚬ X,
  ): (NonAbstractType[X] |*| NonAbstractType[X]) -⚬ NonAbstractType[X] = {
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
                                                            case Left(bx) => // `b` is type mismatch
                                                              mismatch(unit(x) |*| mismatch(bx))
                                                          }
                                                        case Left(ax) => // `a` is type mismatch
                                                          b switch {
                                                            case Right(y) => // `b` is unit
                                                              mismatch(mismatch(ax) |*| unit(y))
                                                            case Left(bx) => // `b` is type mismatch
                                                              mismatch(mismatch(ax) |*| mismatch(bx))
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

  def output[X](
    outputX: X -⚬ Val[Type],
  ): NonAbstractType[X] -⚬ Val[Type] = rec { self =>
    λ { x =>
      unpack(x) switch {
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
                    case Right(x) => // fix or pfix
                      x switch {
                        case Left(tf) =>
                          tf :>> mapVal { tf => Type.fix(tf.vmap(Label.ScalaTParam(_))) }
                        case Right(tf |*| p) =>
                          (tf ** outputX(p)) :>> mapVal { case (tf, p) =>
                            Type.fix(TypeFun.appFst(tf.vmap(Label.ScalaTParam(_)), TypeFun.fromExpr(p)))
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

  def close[X](
    closeX: X -⚬ Done,
  ): NonAbstractType[X] -⚬ Done = rec { self =>
    λ { t =>
      unpack(t) switch {
        case Right(a |*| b) => join(closeX(a) |*| closeX(b))
        case Left(t) => t switch {
          case Right(a |*| b) => join(closeX(a) |*| closeX(b))
          case Left(t) => t switch {
            case Right(a |*| b) => join(closeX(a) |*| closeX(b))
            case Left(t) => t switch {
              case Right(t) =>
                t switch {
                  case Left(f) => neglect(f)
                  case Right(f |*| x) => join(neglect(f) |*| closeX(x))
                }
              case Left(t) => t switch {
                case Right(x) => x
                case Left(t) => t switch {
                  case Right(x) => x
                  case Left(t) => t switch {
                    case Right(x) => x
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

  def awaitPosFst[X](
    g: (Done |*| X) -⚬ X,
  ): (Done |*| NonAbstractType[X]) -⚬ NonAbstractType[X] = rec { self =>
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

  given junctionNonAbstractType[X](using
    X: Junction.Positive[X],
  ): Junction.Positive[NonAbstractType[X]] with {
    override def awaitPosFst: (Done |*| NonAbstractType[X]) -⚬ NonAbstractType[X] =
      NonAbstractType.awaitPosFst[X](X.awaitPosFst)
  }

  class compilationTarget[T](
    splitT: T -⚬ (T |*| T),
    lift: NonAbstractType[T] -⚬ T,
    absType: Label => (One -⚬ T),
  ) {
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

    val typeAlgebra: TypeAlgebra.Of[ScalaTypeParam, Arr, T, |*|, One] =
      new TypeAlgebra[ScalaTypeParam, Arr] {
        override type Type = T
        override type <*>[A, B] = A |*| B
        override type None = One

        override def unit: Arr[One, T] =
          done > λ { case +(d) => d |*| lift(NonAbstractType.unit(d)) }
        override def int: Arr[One, T] =
          done > λ { case +(d) => d |*| lift(NonAbstractType.int(d)) }
        override def string: Arr[One, T] =
          done > λ { case +(d) => d |*| lift(NonAbstractType.string(d)) }
        override def pair: Arr[T |*| T, T] =
          λ { case t |*| u => constant(done) |*| lift(NonAbstractType.pair(t |*| u)) }
        override def sum: Arr[T |*| T, T] =
          λ { case t |*| u => constant(done) |*| lift(NonAbstractType.either(t |*| u)) }
        override def recCall: Arr[T |*| T, T] =
          λ { case t |*| u => constant(done) |*| lift(NonAbstractType.recCall(t |*| u)) }
        override def fix(f: TypeFun[●, ●]): Arr[One, T] =
          const(f) > NonAbstractType.fix > lift > introFst(done)
        override def pfix(f: TypeFun[● × ●, ●]): Arr[T, T] =
          introFst(const(f)) > NonAbstractType.pfix > lift > introFst(done)
        override def abstractTypeName(name: ScalaTypeParam): Arr[One, T] =
          absType(Label.ScalaTParam(name)) > introFst(done)

        override given category: SymmetricMonoidalCategory[Arr, |*|, One] =
          compilationTarget.this.category
      }

    sealed trait as[K, Q]

    case object Map_○ extends as[○, One]
    case object Map_● extends as[●, T]
    case class Pair[K1, K2, Q1, Q2](
      f1: K1 as Q1,
      f2: K2 as Q2,
    ) extends as[K1 × K2, Q1 |*| Q2]

    def split[K, Q](kq: K as Q): Arr[Q, Q |*| Q] =
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

  given TypeOps[NonAbstractType, Type] with {
    override def map[A, B](f: A -⚬ B): NonAbstractType[A] -⚬ NonAbstractType[B] =
      NonAbstractType.map(f)

    override def merge[A](
      f: (A |*| A) -⚬ A,
    ): (NonAbstractType[A] |*| NonAbstractType[A]) -⚬ NonAbstractType[A] =
      NonAbstractType.merge(f)

    override def split[A](f: A -⚬ (A |*| A)): NonAbstractType[A] -⚬ (NonAbstractType[A] |*| NonAbstractType[A]) =
      NonAbstractType.split(f)

    override def output[A](f: A -⚬ Val[Type]): NonAbstractType[A] -⚬ Val[Type] =
      NonAbstractType.output(f)

    override def close[A](f: A -⚬ Done): NonAbstractType[A] -⚬ Done =
      NonAbstractType.close(f)

    override def awaitPosFst[A](f: (Done |*| A) -⚬ A): (Done |*| NonAbstractType[A]) -⚬ NonAbstractType[A] =
      NonAbstractType.awaitPosFst(f)
  }
}
