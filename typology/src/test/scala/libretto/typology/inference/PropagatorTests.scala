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
          case Right(xxx) => injectL(selfRef[V, X](xxx))
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
          case Right(xxx) => injectL(selfRef[V, X](xxx))
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

      private def selfRef[A]: Val[Label] -⚬ IT[A] =
        InferenceSupport.selfRef[Val[Label], A]

      override def split[A]: Sub[A, A |*| A] -⚬ (IT[A] =⚬ (IT[A] |*| IT[A])) =
        λ { case *(f) =>
          λ.closure.rec { self => t =>
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

      override def merge[A]: Sub[A |*| A, A] -⚬ ((IT[A] |*| IT[A]) =⚬ IT[A]) =
        λ { case *(f) =>
          λ.closure { case a |*| b =>
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
        }

      override def map[A, B]: Sub[A, B] -⚬ (IT[A] =⚬ IT[B]) =
        λ { case *(f) =>
          λ.closure.rec { self =>
            { t =>
              switch ( unpack(t) )
                .is { case InR(v)                 => selfRef(v) }
                .is { case InL(InR(x |*| y))      => mismatch(self(x) |*| self(y)) }
                .is { case InL(InL(InL(a |*| b))) => pair(f(a) |*| f(b)) }
                .is { case InL(InL(InR(a |*| b))) => recCall(f(a) |*| f(b)) }
                .end
            }
          }
        }

      override def mapWith[X, A, B](using
        X: CloseableCosemigroup[X],
      ): Sub[X |*| A, B] -⚬ ((X |*| IT[A]) =⚬ IT[B]) =
        λ { case *(f) =>
          λ.closure.rec { self =>
            { case +(x) |*| t =>
              switch ( unpack(t) )
                .is { case InR(v)                 => selfRef(v waitFor X.close(x)) }
                .is { case InL(InR(y |*| z))      => mismatch(self(x |*| y) |*| self(x |*| z)) }
                .is { case InL(InL(InL(a |*| b))) => pair(f(x |*| a) |*| f(x |*| b)) }
                .is { case InL(InL(InR(a |*| b))) => recCall(f(x |*| a) |*| f(x |*| b)) }
                .end
            }
          }
        }

      override def forbiddenSelfReference[A]: Val[Label] -⚬ IT[A] =
        selfRef

      override def output[A]: Sub[A, Val[Type]] -⚬ (IT[A] =⚬ Val[Type]) =
        λ { case *(f) =>
          λ.closure.rec { self =>
            { t =>
              switch ( unpack(t) )
                .is { case InR(v)                 => v |> mapVal { v => Type.ForbiddenSelfRef(v) } }
                .is { case InL(InR(x |*| y))      => (self(x) ** self(y)) |> mapVal { case (x, y) => Type.Mismatch(x, y) } }
                .is { case InL(InL(InL(a |*| b))) => (f(a) ** f(b)) |> mapVal { case (a, b) => Type.Pair(a, b) } }
                .is { case InL(InL(InR(a |*| b))) => (f(a) ** f(b)) |> mapVal { case (a, b) => Type.RecCall(a, b) } }
                .end
            }
          }
        }

      override def close[A]: Sub[A, Done] -⚬ (IT[A] =⚬ Done) =
        λ { case *(f) =>
          λ.closure.rec { self =>
            { t =>
              switch ( unpack(t) )
                .is { case InR(v)                 => neglect(v) }
                .is { case InL(InR(x |*| y))      => (self(x) |*| self(y)) |> join }
                .is { case InL(InL(InL(a |*| b))) => (f(a) |*| f(b)) |> join }
                .is { case InL(InL(InR(a |*| b))) => (f(a) |*| f(b)) |> join }
                .end
            }
          }
        }

      override def awaitPosFst[A]: Sub[Done |*| A, A] -⚬ ((Done |*| IT[A]) =⚬ IT[A]) =
        λ { case *(f) =>
          λ.closure.rec { self =>
            { case d |*| t =>
              switch ( unpack(t) )
                .is { case InR(v)                 => selfRef(v waitFor d) }
                .is { case InL(InR(x |*| y))      => mismatch(self(d |*| x) |*| y) }
                .is { case InL(InL(InL(a |*| b))) => pair(f(d |*| a) |*| b) }
                .is { case InL(InL(InR(a |*| b))) => recCall(f(d |*| a) |*| b) }
                .end
            }
          }
        }
    }
  end InferenceSupport

  import InferenceSupport.{IType, isPair, isRecCall, pair, recCall}

  override def testCases(using kit: StarterTestKit): scala.List[(String, TestCase[kit.type])] = {
    import kit.Outcome
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
        label <- l.append(pg.unwrapLabel).expectVal
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
            t <- port.expectVal
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
            t <- port.expectVal
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
            t <- port.expectVal
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
            t <- port.expectVal
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
            ts <- port.expectVal
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
            ts <- port.expectVal
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
            ts <- port.expectVal
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
            ts <- port.expectVal
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
            ts <- port.expectVal
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
            ts <- port.expectVal
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
            ts <- port.expectVal
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
            ts <- port.expectVal
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
            ts <- port.expectVal
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
          val (b, t) = port.unzip()
          for {
            b <- b.expectVal
            t <- t.expectVal
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
          val (b, t) = port.unzip()
          for {
            b <- b.expectVal
            t <- t.expectVal
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
          val (t, ts) = port.unzip()
          val (ta, tb) = ts.unzip()
          for {
            ab <- t.append(tap > peek).expectLeft
            ab <- ab.append(isRecCall).expectRight
            (a, b) = ab.unzip()
            ta1 <- a.append(write).expectVal
            tb1 <- b.append(write).expectVal
            ta  <- ta.expectVal
            tb  <- tb.expectVal
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
          val (t, ts)  = port.unzip()
          val (ta, tb) = ts.unzip()
          for {
            fa <- t.append(tap > peek).expectLeft
            fa <- fa.append(isPair).expectRight
            (f, a2) = fa.unzip()
            ab <- f.append(peek).expectLeft
            ab <- ab.append(isRecCall).expectRight
            (a1, b) = ab.unzip()

            ta1 = a1.append(write)
            ta2 = a2.append(write)
            tb0 = b.append(write)

            ta1 <- ta1.expectVal
            ta2 <- ta2.expectVal
            tb0 <- tb0.expectVal
            ta  <- ta.expectVal
            tb  <- tb.expectVal

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
          val (t, ts)  = port.unzip()
          val (fa, b2) = t.unzip()
          val (ta, tb) = ts.unzip()
          for {
            fa <- fa.append(npg.tap > npg.peek).expectLeft
            fa <- fa.append(isPair).expectRight
            (f, a2) = fa.unzip()
            f <- f.append(npg.peek).expectLeft
            ab <- f.append(isRecCall).expectRight
            (a1, b1) = ab.unzip()

            a = (a1 zip a2).append(par(lower, lower) > merge)
            b = (b1 zip b2.append(npg.tap)).append(par(lower, lower) > merge)

            ta1 = a.append(output)
            tb1 = b.append(output)

            ta1 <- ta1.expectVal
            tb1 <- tb1.expectVal
            ta  <- ta.expectVal
            tb  <- tb.expectVal

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
            tu <- port.expectVal
            (t, u) = tu
            _ <- assertMatches(t) { case Type.Mismatch(_, _) => }
            _ <- assertEquals(u, Type.Pair(Type.ForbiddenSelfRef(Label(1)), Type.ForbiddenSelfRef(Label(1))))
          } yield ()
        },
    )
  }
}
