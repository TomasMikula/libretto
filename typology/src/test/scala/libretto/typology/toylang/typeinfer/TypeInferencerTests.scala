package libretto.typology.toylang.typeinfer

import libretto.lambda.util.SourcePos
import libretto.lambda.util.Monad.syntax._
import libretto.scaletto.StarterKit._
import libretto.testing.scalatest.scaletto.ScalatestStarterTestSuite
import libretto.testing.scaletto.StarterTestKit
import libretto.testing.TestCase
import libretto.typology.kinds._
import libretto.typology.toylang.typeinfer.TypeInference.inferTypes
import libretto.typology.toylang.types._
import libretto.typology.toylang.types.generic.{TypeExpr => gte}

class TypeInferencerTests extends ScalatestStarterTestSuite {

  override def testCases(using kit: StarterTestKit): scala.List[(String, TestCase[kit.type])] = {
    import kit.{Outcome, expectDone, expectLeft, expectRight, expectVal}
    import Outcome.{assertEquals, assertLeft, assertRight, failure, success}

    import TypeInference.{Labels, ReboundType, RefinementRequest, Tools, Type, TypeEmitter}
    import Labels.Label

    val tools = Tools.groundInstance
    import tools.{abstractTypeTap, close, makeAbstractType, merge, nested, newAbstractType, output, split, unnest}

    def mkLabel(n: Int): One -⚬ Label =
      tools.label(AbstractTypeLabel(n))

    def label(n: Int)(using
      SourcePos,
      LambdaContext,
    ): $[Label] =
      constant(mkLabel(n))

    def assertAbstract(t: Type)(using SourcePos): Outcome[AbstractTypeLabel] =
      t.value match {
        case gte.AbstractType(label) => assertRight(label)
        case other                   => failure(s"Expected abstract type, got $other")
      }

    def assertAbstractEquals(t: Type, expectedLabel: Int)(using SourcePos): Outcome[Unit] =
      assertAbstract(t) flatMap { label =>
        assertEquals(label.value, expectedLabel)
      }

    def assertLabelEquals(using exn: kit.bridge.Execution)(l: exn.OutPort[Label], expectedValue: Int)(using SourcePos): Outcome[Unit] =
      expectVal(OutPort.map(l)(Labels.unwrapOriginal)) flatMap { label =>
        assertRight(label) flatMap { label =>
          assertEquals(label.value, expectedValue)
        }
      }

    List(
      "newAbstractType" -> TestCase
        .interactWith {
          val prg: Done -⚬ Val[Type] = λ { d =>
            val x1 |*| t |*| x2 = newAbstractType(label(1))
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
            val x1 |*| t |*| x2 = nested.newAbstractType(label(1))
            t
              .waitFor(d)
              .waitFor(nested.close(x1))
              .waitFor(nested.close(x2))
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
            val x1 |*| t |*| x2 = nested.newAbstractType(label(1))
            t
              .waitFor(d)
              .waitFor(close(unnest(x1)))
              .waitFor(close(unnest(x2)))
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

      "split and merge abstract type" -> TestCase
        .interactWith {
          λ { d =>
            val a |*| t = abstractTypeTap(label(1))
            val b = merge(split(a))
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

      "split abstract type, refine one end with another abstract type" -> TestCase
        .interactWith {
          λ { start =>
            val a |*| resp = makeAbstractType(label(2) waitFor start)
            split(a) |*| resp
          }
        }
        .via { exn ?=> port =>
          def expectAbstractOutbound[T](t: exn.OutPort[TypeEmitter[T]]) =
            expectRight(OutPort.map(t)(TypeEmitter.unpack))

          def expectAbstractInbound[T](t: exn.OutPort[ReboundType[T]]) =
            expectRight(OutPort.map(t)(ReboundType.unpack))

          val (a, resp) = OutPort.split(port)
          val (a1, a2)  = OutPort.split(a)
          for {
            // expect both are abstract
            a1 <- expectAbstractOutbound(a1)
            (l1, req1) = OutPort.split(a1)
            a2 <- expectAbstractOutbound(a2)
            (l2, req2) = OutPort.split(a2)

            // and have the correct label
            _ <- assertLabelEquals(l1, 2)
            _ <- assertLabelEquals(l2, 2)

            // decline refinement request of the first one
            resp1 = OutPort.map(req1)(RefinementRequest.decline)

            // refine the second one by another abstract type
            sink2 = OutPort.map(req2)(RefinementRequest.grant)
            l0 = OutPort.constant(mkLabel(1))
            (t2, resp2) = OutPort.split(OutPort.map(l0)(ReboundType.makeAbstractType[Done]))
            () = OutPort.discardOne(OutPort.map(OutPort.pair(t2, sink2))(supply))

            // the first one should now be refined
            a1 <- expectLeft(resp1)
            // to the new abstract type
            a1 <- expectAbstractOutbound(a1)
            (l1, req1) = OutPort.split(a1)
            _ <- assertLabelEquals(l1, 1)
            // which we decline to refine
            resp1 = OutPort.map(req1)(RefinementRequest.decline)

            // the source abstract type should now be refined
            a <- expectLeft(resp)
            // to the new abstract type
            a <- expectAbstractInbound(a)
            (l, req) = OutPort.split(a)
            _ <- assertLabelEquals(l, 1)
            // which we decline to refine
            resp = OutPort.map(req)(RefinementRequest.decline)

            // there was no refinement of the new abstract type
            resp2 <- expectRight(resp2).flatMap(expectLeft(_))
            // we choose to provide type argument
            nd = OutPort.map(resp2)(contrapositive(injectR) > doubleDemandElimination)
            () = OutPort.discardOne(OutPort.map(nd)(contrapositive(done) > unInvertOne))

            // neither was the other output reinvigorated; we are asked to provide a type argument
            nd <- expectRight(resp1)
            // we provide a type argument
            () = OutPort.discardOne(OutPort.map(nd)(contrapositive(done) > unInvertOne))

            // the source type was not reinvigorated
            nnd <- expectRight(resp)
            // we receive the (merged) type argument
            d = OutPort.map(nnd)(doubleDemandElimination)
            _ <- expectDone(d)
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
    )
  }
}
