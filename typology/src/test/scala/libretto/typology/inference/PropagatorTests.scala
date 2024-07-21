package libretto.typology.inference

import libretto.lambda.util.SourcePos
import libretto.scaletto.StarterKit.*
import libretto.testing.scalatest.scaletto.ScalatestStarterTestSuite
import libretto.testing.scaletto.StarterTestKit
import libretto.testing.TestCase
import libretto.typology.inference.Propagator

class PropagatorTests extends ScalatestStarterTestSuite {

  case class Label(value: Int)
  object Label:
    given Ordering[Label] =
      { (a, b) => a.value compare b.value }

  enum Type:
    case Pair(a: Type, b: Type)
    case RecCall(a: Type, b: Type)
    case Abstr(label: Label)
    case Mismatch(x: Type, y: Type)
    case ForbiddenSelfRef(v: Label)

  object InferenceSupport:
    private type ITypeF[V, T, X] =
      (T |*| T)     // pair
      |+| (T |*| T) // recCall
      |+| (X |*| X) // mismatch
      |+| V         // forbidden self-reference

    opaque type IType[V, T] = Rec[ITypeF[V, T, _]]

    private def pack[V, T]: ITypeF[V, T, IType[V, T]] -⚬ IType[V, T] =
      dsl.pack[ITypeF[V, T, _]]

    private def unpack[V, T]: IType[V, T] -⚬ ITypeF[V, T, IType[V, T]] =
      dsl.unpack[ITypeF[V, T, _]]

    def pair[V, X]: (X |*| X) -⚬ IType[V, X] =
      injectL > injectL > injectL > pack

    def recCall[V, X]: (X |*| X) -⚬ IType[V, X] =
      injectR > injectL > injectL > pack

    def mismatch[V, X]: (IType[V, X] |*| IType[V, X]) -⚬ IType[V, X] =
      injectR > injectL > pack

    def selfRef[V, X]: V -⚬ IType[V, X] =
      injectR > pack

    def isPair[V, X]: IType[V, X] -⚬ (IType[V, X] |+| (X |*| X)) =
      λ { t =>
        unpack(t) either {
          case Right(xxx) => injectL(selfRef(xxx))
          case Left(t) => t either {
            case Right(xxx) => injectL(mismatch(xxx))
            case Left(t) => t either {
              case Left(x |*| y) => injectR(x |*| y)
              case Right(rc)     => injectL(recCall(rc))
            }
          }
        }
      }

    def isRecCall[V, X]: IType[V, X] -⚬ (IType[V, X] |+| (X |*| X)) =
      λ { t =>
        unpack(t) either {
          case Right(xxx) => injectL(selfRef(xxx))
          case Left(t) => t either {
            case Right(xxx) => injectL(mismatch(xxx))
            case Left(t) => t either {
              case Left(xy)      => injectL(pair(xy))
              case Right(x |*| y) => injectR(x |*| y)
            }
          }
        }
      }

    given TypeOps[IType[Val[Label], _], Type, Label] with {
      type IT[A] = IType[Val[Label], A]

      override def split[A](f: A -⚬ (A |*| A)): IT[A] -⚬ (IT[A] |*| IT[A]) =
        rec { self =>
          λ { case t =>
            unpack(t) either {
              case Right(lbl) =>
                val l1 |*| l2 = dup(lbl)
                selfRef(l1) |*| selfRef(l2)
              case Left(t) => t either {
                case Right(x |*| y) =>
                  val x1 |*| x2 = self(x)
                  val y1 |*| y2 = self(y)
                  mismatch(x1 |*| y1) |*| mismatch(x2 |*| y2)
                case Left(t) => t either {
                  case Left(a |*| b)  =>
                    val a1 |*| a2 = f(a)
                    val b1 |*| b2 = f(b)
                    pair(a1 |*| b1) |*| pair(a2 |*| b2)
                  case Right(a |*| b) =>
                    val a1 |*| a2 = f(a)
                    val b1 |*| b2 = f(b)
                    recCall(a1 |*| b1) |*| recCall(a2 |*| b2)
                }
              }
            }
          }
        }

      override def merge[A](f: (A |*| A) -⚬ A): (IT[A] |*| IT[A]) -⚬ IT[A] =
        λ { case a |*| b =>
          unpack(a) either {
            case Right(xxx) => mismatch(selfRef(xxx) |*| b)
            case Left(a) => unpack(b) either {
              case Right(yyy) => mismatch(pack(injectL(a)) |*| selfRef(yyy))
              case Left(b) => a either {
                case Right(xxx) => mismatch(mismatch(xxx) |*| pack(injectL(b)))
                case Left(a) => a either {
                  case Left(a1 |*| a2) =>
                    b either {
                      case Right(yyy) => mismatch(pair(a1 |*| a2) |*| mismatch(yyy))
                      case Left(b) => b either {
                        case Left(b1 |*| b2)  => pair(f(a1 |*| b1) |*| f(a2 |*| b2))
                        case Right(bi |*| bo) => mismatch(pair(a1 |*| a2) |*| recCall(bi |*| bo))
                      }
                    }
                  case Right(ai |*| ao) =>
                    b either {
                      case Right(yyy) => mismatch(recCall(ai |*| ao) |*| mismatch(yyy))
                      case Left(b) => b either {
                        case Left(b1 |*| b2)  => mismatch(recCall(ai |*| ao) |*| pair(b1 |*| b2))
                        case Right(bi |*| bo) => recCall(f(ai |*| bi) |*| f(ao |*| bo))
                      }
                    }
                }
              }
            }
          }
        }

      override def map[A, B](f: A -⚬ B): IT[A] -⚬ IT[B] =
        rec { self =>
          λ { t =>
            unpack(t) either {
              case Right(v) => selfRef(v)
              case Left(t) => t either {
                case Right(x |*| y) => mismatch(self(x) |*| self(y))
                case Left(t) => t either {
                  case Left(a |*| b)  => pair(f(a) |*| f(b))
                  case Right(a |*| b) => recCall(f(a) |*| f(b))
                }
              }
            }
          }
        }

      override def mapWith[X, A, B](f: (X |*| A) -⚬ B)(using
        X: CloseableCosemigroup[X],
      ): (X |*| IT[A]) -⚬ IT[B] =
        rec { self =>
          λ { case +(x) |*| t =>
            unpack(t) either {
              case Right(v) => selfRef(v waitFor X.close(x))
              case Left(t) => t either {
                case Right(y |*| z) => mismatch(self(x |*| y) |*| self(x |*| z))
                case Left(t) => t either {
                  case Left(a |*| b)  => pair(f(x |*| a) |*| f(x |*| b))
                  case Right(a |*| b) => recCall(f(x |*| a) |*| f(x |*| b))
                }
              }
            }
          }
        }

      override def forbiddenSelfReference[A]: Val[Label] -⚬ IT[A] =
        selfRef

      override def output[A](f: A -⚬ Val[Type]): IT[A] -⚬ Val[Type] =
        rec { self =>
          λ {t =>
            unpack(t) either {
              case Right(v) => v :>> mapVal { v => Type.ForbiddenSelfRef(v) }
              case Left(t) => t either {
                case Right(x |*| y) => (self(x) ** self(y)) :>> mapVal { case (x, y) => Type.Mismatch(x, y) }
                case Left(t) => t either {
                  case Left(a |*| b)  => (f(a) ** f(b)) :>> mapVal { case (a, b) => Type.Pair(a, b) }
                  case Right(a |*| b) => (f(a) ** f(b)) :>> mapVal { case (a, b) => Type.RecCall(a, b) }
                }
              }
            }
          }
        }

      override def close[A](f: A -⚬ Done): IT[A] -⚬ Done =
        rec { self =>
          λ { t =>
            unpack(t) either {
              case Right(v) => neglect(v)
              case Left(t) => t either {
                case Right(x |*| y) => (self(x) |*| self(y)) :>> join
                case Left(t) => t either {
                  case Left(a |*| b)  => (f(a) |*| f(b)) :>> join
                  case Right(a |*| b) => (f(a) |*| f(b)) :>> join
                }
              }
            }
          }
        }

      override def awaitPosFst[A](f: (Done |*| A) -⚬ A): (Done |*| IT[A]) -⚬ IT[A] =
        rec { self =>
          λ { case d |*| t =>
            unpack(t) either {
              case Right(v) => selfRef(v waitFor d)
              case Left(t) => t either {
                case Right(x |*| y) => mismatch(self(d |*| x) |*| y)
                case Left(t) => t either {
                  case Left(a |*| b)  => pair(f(d |*| a) |*| b)
                  case Right(a |*| b) => recCall(f(d |*| a) |*| b)
                }
              }
            }
          }
        }
    }
  end InferenceSupport

  import InferenceSupport.{IType, isPair, isRecCall, pair, recCall}

  override def testCases(using kit: StarterTestKit): scala.List[(String, TestCase[kit.type])] = {
    import kit.{Outcome, expectLeft, expectRight, expectVal}
    import Outcome.{assertEquals, assertMatches, assertRight, failure, success}

    val pg =
      libretto.typology.inference.Propagator.instance[IType[Val[Label], _], Type, Label](Type.Abstr(_))
    import pg.{
      Tp,
      abstractTypeTap,
      close,
      merge,
      nested,
      output,
      peek,
      split,
      tap,
      write,
    }

    val nested = pg.nested
    import nested.{lower, propagator => npg, unnest}

    extension (pg: Propagator[IType[Val[Label], _], Type, Label])
      def mkLabel(n: Int): One -⚬ pg.Label =
        pg.label(Label(n))

      def lbl(n: Int)(using
        SourcePos,
        LambdaContext,
      ): $[pg.Label] =
        constant(mkLabel(n))

      def abstractTypeSplit: pg.Label -⚬ (pg.Tp |*| Val[Type] |*| pg.Tp) =
        pg.abstractTypeTap > λ { case t |*| o =>
          val t1 |*| t2 = pg.split(t)
          t1 |*| o |*| t2
        }


    def label(n: Int)(using
      SourcePos,
      LambdaContext,
    ): $[pg.Label] =
      pg.lbl(n)

    def assertAbstract(t: Type)(using SourcePos): Outcome[Label] =
      t match {
        case Type.Abstr(label) => success(label)
        case other            => failure(s"Expected abstract type, got $other")
      }

    def assertAbstractEquals(t: Type, expectedLabel: Int)(using SourcePos): Outcome[Unit] =
      assertAbstract(t) flatMap { label =>
        assertEquals(label.value, expectedLabel)
      }

    def assertLabelEquals(using exn: kit.bridge.Execution)(
      l: exn.OutPort[pg.Label],
      expectedValue: Int,
    )(using SourcePos): Outcome[Unit] =
      for {
        label <- expectVal(OutPort.map(l)(pg.unwrapLabel))
        u <- assertEquals(label.value, expectedValue)
      } yield u

    List(
      "newAbstractType" -> TestCase
        .interactWith {
          val prg: Done -⚬ Val[Type] = λ { d =>
            val x1 |*| t |*| x2 = pg.abstractTypeSplit(label(1))
            t
              .waitFor(d)
              .waitFor(close(x1))
              .waitFor(close(x2))
          }
          prg
        }
        .via { port =>
          for {
            t <- expectVal(port)
            _ <- assertAbstractEquals(t, 1)
          } yield ()
        },

      "nested.newAbstractType" -> TestCase
        .interactWith {
          val prg: Done -⚬ Val[Type] = λ { d =>
            val x1 |*| t |*| x2 = npg.abstractTypeSplit(npg.lbl(1))
            t
              .waitFor(d)
              .waitFor(npg.close(x1))
              .waitFor(npg.close(x2))
          }
          prg
        }
        .via { port =>
          for {
            t <- expectVal(port)
            _ <- assertAbstractEquals(t, 1)
          } yield ()
        },

      "nested.newAbstractType unnest before close" -> TestCase
        .interactWith {
          val prg: Done -⚬ Val[Type] = λ { d =>
            val x1 |*| t |*| x2 = npg.abstractTypeSplit(npg.lbl(1))
            t
              .waitFor(d)
              .waitFor(close(nested.unnest(x1)))
              .waitFor(close(nested.unnest(x2)))
          }
          prg
        }
        .via { port =>
          for {
            t <- expectVal(port)
            _ <- assertAbstractEquals(t, 1)
          } yield ()
        },

      "merge abstract types" -> TestCase
        .interactWith {
          val prg: Done -⚬ Val[Type] = λ { d =>
            val a |*| t1 = abstractTypeTap(label(1))
            val b |*| t2 = abstractTypeTap(label(2))
            val t = merge(a |*| b)
            output(t)
              .waitFor(d)
              .waitFor(neglect(t1))
              .waitFor(neglect(t2))
          }
          prg
        }
        .via { port =>
          for {
            t <- expectVal(port)
            _ <- assertAbstractEquals(t, 1)
          } yield ()
        },

      "merge 3 abstract types" -> TestCase
        .interactWith {
          λ { d =>
            val a |*| t1 = abstractTypeTap(label(1))
            val b |*| t2 = abstractTypeTap(label(2))
            val c |*| t3 = abstractTypeTap(label(3))
            val t = merge(a |*| merge(b |*| c))
            output(t) ** (t1 ** t2 ** t3)
              .waitFor(d)
          }
        }
        .via { port =>
          for {
            ts <- expectVal(port)
            (t, ((a, b), c)) = ts
            _ <- assertAbstractEquals(t, 1)
            _ <- assertAbstractEquals(a, 1)
            _ <- assertAbstractEquals(b, 1)
            _ <- assertAbstractEquals(c, 1)
          } yield ()
        },

      "merge 4 abstract types" -> TestCase
        .interactWith {
          λ { start =>
            val a |*| t1 = abstractTypeTap(label(1))
            val b |*| t2 = abstractTypeTap(label(2))
            val c |*| t3 = abstractTypeTap(label(3))
            val d |*| t4 = abstractTypeTap(label(4))
            val t = merge(merge(a |*| b) |*| merge(c |*| d))
            output(t) ** ((t1 ** t2) ** (t3 ** t4))
              .waitFor(start)
          }
        }
        .via { port =>
          for {
            ts <- expectVal(port)
            (t, ((a, b), (c, d))) = ts
            _ <- assertAbstractEquals(t, 1)
            _ <- assertAbstractEquals(a, 1)
            _ <- assertAbstractEquals(b, 1)
            _ <- assertAbstractEquals(c, 1)
            _ <- assertAbstractEquals(d, 1)
          } yield ()
        },

      "split abstract type" -> TestCase
        .interactWith {
          λ { d =>
            val a |*| t = abstractTypeTap(label(1))
            val x |*| y = split(a)
            (t ** output(x) ** output(y))
              .waitFor(d)
          }
        }
        .via { port =>
          for {
            ts <- expectVal(port)
            ((t, x), y) = ts
            vt <- assertAbstract(t)
            vx <- assertAbstract(x)
            vy <- assertAbstract(y)
            _ <- assertAbstractEquals(t, 1)
            _ <- assertAbstractEquals(x, 1)
            _ <- assertAbstractEquals(y, 1)
          } yield ()
        },

      "split abstract type into 3" -> TestCase
        .interactWith {
          λ { d =>
            val a |*| t = abstractTypeTap(label(1))
            val x |*| yz = split(a)
            val y |*| z = split(yz)
            (t ** output(x) ** output(y) ** output(z))
              .waitFor(d)
          }
        }
        .via { port =>
          for {
            ts <- expectVal(port)
            (((t, x), y), z) = ts
            _ <- assertAbstractEquals(t, 1)
            _ <- assertAbstractEquals(x, 1)
            _ <- assertAbstractEquals(y, 1)
            _ <- assertAbstractEquals(z, 1)
          } yield ()
        },

      "split abstract type into 4" -> TestCase
        .interactWith {
          λ { start =>
            val x |*| t = abstractTypeTap(label(1))
            val ab |*| cd = split(x)
            val a |*| b = split(ab)
            val c |*| d = split(cd)
            (t ** ((output(a) ** output(b)) ** (output(c) ** output(d))))
              .waitFor(start)
          }
        }
        .via { port =>
          for {
            ts <- expectVal(port)
            (t, ((a, b), (c, d))) = ts
            _ <- assertAbstractEquals(t, 1)
            _ <- assertAbstractEquals(a, 1)
            _ <- assertAbstractEquals(b, 1)
            _ <- assertAbstractEquals(c, 1)
            _ <- assertAbstractEquals(d, 1)
          } yield ()
        },

      "split and unnest abstract type" -> TestCase
        .interactWith {
          λ { d =>
            val a |*| t = npg.abstractTypeTap(npg.lbl(1))
            val a1 |*| a2 = npg.split(a)
            val b = merge(unnest(a1) |*| unnest(a2))
            (t ** (output(unnest(a1)) ** output(unnest(a2))))
              .waitFor(d)
          }
        }
        .via { port =>
          for {
            ts <- expectVal(port)
            (t, (a1, a2)) = ts
            _ <- assertAbstractEquals(t, 1)
            _ <- assertAbstractEquals(a1, 1)
            _ <- assertAbstractEquals(a2, 1)
          } yield ()
        },

      "split and merge abstract type" -> TestCase
        .interactWith {
          λ { d =>
            val a |*| t = abstractTypeTap(label(1))
            val a1 |*| a2 = split(a)
            val b = merge(a1 |*| a2)
            (t ** output(b))
              .waitFor(d)
          }
        }
        .via { port =>
          for {
            ts <- expectVal(port)
            (t, b) = ts
            _ <- assertAbstractEquals(t, 1)
            _ <- assertAbstractEquals(b, 1)
          } yield ()
        },

      "split abstract type, merge with another abstract type" -> TestCase
        .interactWith {
          λ { start =>
            val a |*| ta = abstractTypeTap(label(1))
            val b |*| tb = abstractTypeTap(label(2))
            val a1 |*| a2 = split(a)
            val c = merge(a2 |*| b)
            ((output(c) ** output(a1)) ** (ta ** tb))
              .waitFor(start)
          }
        }
        .via { port =>
          for {
            ts <- expectVal(port)
            ((c, a), (t1, t2)) = ts
            _ <- assertAbstractEquals(c, 1)
            _ <- assertAbstractEquals(a, 1)
            _ <- assertAbstractEquals(t1, 1)
            _ <- assertAbstractEquals(t2, 1)
          } yield ()
        },

      "split two abstract types, merge one from each" -> TestCase
        .interactWith {
          λ { start =>
            val a |*| ta = abstractTypeTap(label(1))
            val b |*| tb = abstractTypeTap(label(2))
            val a1 |*| a2 = split(a)
            val b1 |*| b2 = split(b)
            val c = merge(a2 |*| b2)
            (output(c) ** (output(a1) ** output(b1)) ** (ta ** tb))
              .waitFor(start)
          }
        }
        .via { port =>
          for {
            ts <- expectVal(port)
            ((t, (a, b)), (t1, t2)) = ts
            _ <- assertAbstractEquals(t, 1)
            _ <- assertAbstractEquals(a, 1)
            _ <- assertAbstractEquals(b, 1)
            _ <- assertAbstractEquals(t1, 1)
            _ <- assertAbstractEquals(t2, 1)
          } yield ()
        },

      "unnest" -> TestCase
        .interactWith {
          λ { d =>
            val a |*| t = npg.abstractTypeTap(npg.lbl(1))
            val b = nested.unnest(a)
            output(b) |*| (t waitFor d)
          }
        }
        .via { port =>
          val (b, t) = OutPort.split(port)
          for {
            b <- expectVal(b)
            t <- expectVal(t)
            _ <- assertAbstractEquals(b, 1)
            _ <- assertAbstractEquals(t, 1)
          } yield ()
        },

      "split abstract type, unnest, merge" -> TestCase
        .interactWith {
          λ { d =>
            val a |*| t = npg.abstractTypeTap(npg.lbl(1))
            val a1 |*| a2 = npg.split(a)
            val b1 = unnest(a1)
            val b2 = unnest(a2)
            val b = merge(b1 |*| b2)
            output(b) |*| (t waitFor d)
          }
        }
        .via { port =>
          val (b, t) = OutPort.split(port)
          for {
            b <- expectVal(b)
            t <- expectVal(t)
            _ <- assertAbstractEquals(b, 1)
            _ <- assertAbstractEquals(t, 1)
          } yield ()
        },

      "construct and deconstruct RecCall[A, B]" -> TestCase
        .interactWith {
          λ { start =>
            val a |*| ta = abstractTypeTap(label(1))
            val b |*| tb = abstractTypeTap(label(2))
            Tp(recCall(a |*| b))
              |*| (ta |*| tb.waitFor(start))
          }
        }
        .via { port =>
          val (t, ts) = OutPort.split(port)
          val (ta, tb) = OutPort.split(ts)
          for {
            ab <- expectLeft(OutPort.map(t)(tap > peek))
            ab <- expectRight(OutPort.map(ab)(isRecCall))
            (a, b) = OutPort.split(ab)
            ta1 <- expectVal(OutPort.map(a)(write))
            tb1 <- expectVal(OutPort.map(b)(write))
            ta  <- expectVal(ta)
            tb  <- expectVal(tb)
            _ <- assertAbstractEquals(ta, 1)
            _ <- assertAbstractEquals(ta1, 1)
            _ <- assertAbstractEquals(tb, 2)
            _ <- assertAbstractEquals(tb1, 2)
          } yield ()
        },

      "construct and deconstruct (RecCall[A, B], A)" -> TestCase
        .interactWith {
          λ { start =>
            val a |*| ta = abstractTypeTap(label(1))
            val b |*| tb = abstractTypeTap(label(2))
            val a1 |*| a2 = split(a)
            Tp(pair(Tp(recCall(a1 |*| b)) |*| a2))
              |*| (ta |*| tb.waitFor(start))
          }
        }
        .via { port =>
          val (t, ts)  = OutPort.split(port)
          val (ta, tb) = OutPort.split(ts)
          for {
            fa <- expectLeft(OutPort.map(t)(tap > peek))
            fa <- expectRight(OutPort.map(fa)(isPair))
            (f, a2) = OutPort.split(fa)
            ab <- expectLeft(OutPort.map(f)(peek))
            ab <- expectRight(OutPort.map(ab)(isRecCall))
            (a1, b) = OutPort.split(ab)

            ta1 = OutPort.map(a1)(write)
            ta2 = OutPort.map(a2)(write)
            tb0 = OutPort.map(b)(write)

            ta1 <- expectVal(ta1)
            ta2 <- expectVal(ta2)
            tb0 <- expectVal(tb0)
            ta  <- expectVal(ta)
            tb  <- expectVal(tb)

            _ <- assertAbstractEquals(ta, 1)
            _ <- assertAbstractEquals(ta1, 1)
            _ <- assertAbstractEquals(ta2, 1)
            _ <- assertAbstractEquals(tb, 2)
            _ <- assertAbstractEquals(tb0, 2)
          } yield ()
        },

      "construct and deconstruct (RecCall[A, B], A), merge after deconstruction" -> TestCase
        .interactWith {
          λ { start =>
            val a |*| ta = npg.abstractTypeTap(npg.lbl(1))
            val b |*| tb = npg.abstractTypeTap(npg.lbl(2))
            val a1 |*| a2 = npg.split(a)
            val b1 |*| b2 = npg.split(b)
            npg.Tp(pair(npg.Tp(recCall(a1 |*| b1)) |*| a2)) |*| b2
              |*| (ta |*| tb.waitFor(start))
          }
        }
        .via { port =>
          val (t, ts)  = OutPort.split(port)
          val (fa, b2) = OutPort.split(t)
          val (ta, tb) = OutPort.split(ts)
          for {
            fa <- expectLeft(OutPort.map(fa)(npg.tap > npg.peek))
            fa <- expectRight(OutPort.map(fa)(isPair))
            (f, a2) = OutPort.split(fa)
            f <- expectLeft(OutPort.map(f)(npg.peek))
            ab <- expectRight(OutPort.map(f)(isRecCall))
            (a1, b1) = OutPort.split(ab)

            a = OutPort.map(OutPort.pair(a1, a2))(par(lower, lower) > merge)
            b = OutPort.map(OutPort.pair(b1, OutPort.map(b2)(npg.tap)))(par(lower, lower) > merge)

            ta1 = OutPort.map(a)(output)
            tb1 = OutPort.map(b)(output)

            ta1 <- expectVal(ta1)
            tb1 <- expectVal(tb1)
            ta  <- expectVal(ta)
            tb  <- expectVal(tb)

            _ <- assertAbstractEquals(ta, 1)
            _ <- assertAbstractEquals(ta1, 1)
            _ <- assertAbstractEquals(tb, 2)
            _ <- assertAbstractEquals(tb1, 2)
          } yield ()
        },

      "prevent a = (a, a)" -> TestCase
        .interactWith {
          λ { d =>
            val a |*| t = abstractTypeTap(label(1))
            val a1 |*| a2 = split(a)
            val a3 |*| a4 = split(a2)
            val aa = Tp(pair(a3 |*| a4))
            val u = merge(a1 |*| aa)
            (t ** output(u))
              .waitFor(d)
          }
        }
        .via { port =>
          for {
            tu <- expectVal(port)
            (t, u) = tu
            _ <- assertMatches(t) { case Type.Mismatch(_, _) => }
            _ <- assertEquals(u, Type.Pair(Type.ForbiddenSelfRef(Label(1)), Type.ForbiddenSelfRef(Label(1))))
          } yield ()
        },
    )
  }
}
