package libretto.typology.toylang.typeinfer

import libretto.lambda.util.SourcePos
import libretto.lambda.util.Monad.syntax._
import libretto.scaletto.StarterKit._
import libretto.testing.scalatest.scaletto.ScalatestStarterTestSuite
import libretto.testing.scaletto.StarterTestKit
import libretto.testing.TestCase
import libretto.typology.toylang.terms.TypedFun.Type
import libretto.typology.toylang.types.{AbstractTypeLabel, Label}
import libretto.typology.toylang.types.generic.{TypeExpr => gte}

class TypeInferencerTests extends ScalatestStarterTestSuite {

  override def testCases(using kit: StarterTestKit): scala.List[(String, TestCase[kit.type])] = {
    import kit.{Outcome, expectDone, expectLeft, expectRight, expectVal}
    import Outcome.{assertEquals, assertLeft, assertMatches, assertRight, failure, success}
    import NonAbstractType.{isPair, isRecCall, pair, recCall, given}

    val tools =
      TypeInferencer.instance[NonAbstractType, Type, Label](Type.abstractType)
    import tools.{
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

    val nested = tools.nested
    import nested.{lower, tools => nt, unnest}

    val nn = nt.nested
    import nn.{tools => nnt}

    extension (tools: TypeInferencer[NonAbstractType, Type, Label])
      def mkLabel(n: Int): One -⚬ tools.Label =
        tools.label(Label.Abstr(AbstractTypeLabel(n)))

      def lbl(n: Int)(using
        SourcePos,
        LambdaContext,
      ): $[tools.Label] =
        constant(mkLabel(n))

      def abstractTypeSplit: tools.Label -⚬ (tools.Tp |*| Val[Type] |*| tools.Tp) =
        tools.abstractTypeTap > λ { case t |*| o =>
          val t1 |*| t2 = tools.split(t)
          t1 |*| o |*| t2
        }


    def label(n: Int)(using
      SourcePos,
      LambdaContext,
    ): $[tools.Label] =
      tools.lbl(n)

    def assertAbstract(t: Type)(using SourcePos): Outcome[AbstractTypeLabel] =
      t.value match {
        case gte.AbstractType(label) => assertMatches(label) { case Label.Abstr(l) => l}
        case other                   => failure(s"Expected abstract type, got $other")
      }

    def assertAbstractEquals(t: Type, expectedLabel: Int)(using SourcePos): Outcome[Unit] =
      assertAbstract(t) flatMap { label =>
        assertEquals(label.value, expectedLabel)
      }

    def assertLabelEquals(using exn: kit.bridge.Execution)(
      l: exn.OutPort[tools.Label],
      expectedValue: Int,
    )(using SourcePos): Outcome[Unit] =
      for {
        label <- expectVal(OutPort.map(l)(tools.unwrapLabel))
        label <- assertMatches(label) { case Label.Abstr(l) => l }
        u <- assertEquals(label.value, expectedValue)
      } yield u

    List(
      "newAbstractType" -> TestCase
        .interactWith {
          val prg: Done -⚬ Val[Type] = λ { d =>
            val x1 |*| t |*| x2 = tools.abstractTypeSplit(label(1))
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
            val x1 |*| t |*| x2 = nt.abstractTypeSplit(nt.lbl(1))
            t
              .waitFor(d)
              .waitFor(nt.close(x1))
              .waitFor(nt.close(x2))
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
            val x1 |*| t |*| x2 = nt.abstractTypeSplit(nt.lbl(1))
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
            val a |*| t = nt.abstractTypeTap(nt.lbl(1))
            val a1 |*| a2 = nt.split(a)
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
            val a |*| t = nt.abstractTypeTap(nt.lbl(1))
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
            val a |*| t = nt.abstractTypeTap(nt.lbl(1))
            val a1 |*| a2 = nt.split(a)
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
            val a |*| ta = nt.abstractTypeTap(nt.lbl(1))
            val b |*| tb = nt.abstractTypeTap(nt.lbl(2))
            val a1 |*| a2 = nt.split(a)
            val b1 |*| b2 = nt.split(b)
            nt.Tp(pair(nt.Tp(recCall(a1 |*| b1)) |*| a2)) |*| b2
              |*| (ta |*| tb.waitFor(start))
          }
        }
        .via { port =>
          val (t, ts)  = OutPort.split(port)
          val (fa, b2) = OutPort.split(t)
          val (ta, tb) = OutPort.split(ts)
          for {
            fa <- expectLeft(OutPort.map(fa)(nt.tap > nt.peek))
            fa <- expectRight(OutPort.map(fa)(isPair))
            (f, a2) = OutPort.split(fa)
            f <- expectLeft(OutPort.map(f)(nt.peek))
            ab <- expectRight(OutPort.map(f)(isRecCall))
            (a1, b1) = OutPort.split(ab)

            a = OutPort.map(OutPort.pair(a1, a2))(par(lower, lower) > merge)
            b = OutPort.map(OutPort.pair(b1, OutPort.map(b2)(nt.tap)))(par(lower, lower) > merge)

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
    )
  }
}
