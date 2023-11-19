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

    import Tools.ToolsImpl
    import Tools.ToolsImpl.{ReboundType, RefinementRequest, Type, TypeEmitter}

    val tools =
      // Tools.instance
      TypeInferencer.instance
    import tools.{
      Label,
      abstractTypeSplit,
      abstractTypeTap,
      close,
      closeS,
      isPair,
      isRecCall,
      merge,
      mergeable,
      nested,
      output,
      outputM,
      outputOW,
      outputS,
      pair,
      recCall,
      split,
      splittable,
      tap,
    }

    val nested = tools.nested
    import nested.{tools => nt, unnestM, unnestS}

    val nn = nt.nested
    import nn.{tools => nnt}

    val ti = ToolsImpl.groundInstance

    extension (tools: Tools)
      def mkLabel(n: Int): One -⚬ tools.Label =
        tools.label(AbstractTypeLabel(n))

      def lbl(n: Int)(using
        SourcePos,
        LambdaContext,
      ): $[tools.Label] =
        constant(mkLabel(n))


    def label(n: Int)(using
      SourcePos,
      LambdaContext,
    ): $[tools.Label] =
      tools.lbl(n)

    def assertAbstract(t: Type)(using SourcePos): Outcome[AbstractTypeLabel] =
      t.value match {
        case gte.AbstractType(label) => assertRight(label)
        case other                   => failure(s"Expected abstract type, got $other")
      }

    def assertAbstractEquals(t: Type, expectedLabel: Int)(using SourcePos): Outcome[Unit] =
      assertAbstract(t) flatMap { label =>
        assertEquals(label.value, expectedLabel)
      }

    def assertLabelEquals(using exn: kit.bridge.Execution)(l: exn.OutPort[ti.Label], expectedValue: Int)(using SourcePos): Outcome[Unit] =
      expectVal(OutPort.map(l)(Tools.labels.unwrapOriginal)) flatMap { label =>
        assertRight(label) flatMap { label =>
          assertEquals(label.value, expectedValue)
        }
      }

    List(
      "newAbstractType" -> TestCase
        .interactWith {
          val prg: Done -⚬ Val[Type] = λ { d =>
            val x1 |*| t |*| x2 = abstractTypeSplit(label(1))
            t
              .waitFor(d)
              .waitFor(closeS(x1))
              .waitFor(closeS(x2))
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
              .waitFor(nt.closeS(x1))
              .waitFor(nt.closeS(x2))
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
              .waitFor(close(nested.unnestS(x1)))
              .waitFor(close(nested.unnestS(x2)))
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
            val t = merge(mergeable(a) |*| mergeable(b))
            outputM(t)
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
            val t = merge(mergeable(a) |*| merge(mergeable(b) |*| mergeable(c)))
            outputM(t) ** (t1 ** t2 ** t3)
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
            val t = merge(merge(mergeable(a) |*| mergeable(b)) |*| merge(mergeable(c) |*| mergeable(d)))
            outputM(t) ** ((t1 ** t2) ** (t3 ** t4))
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
            val x |*| y = split(splittable(a))
            (t ** outputS(x) ** outputS(y))
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
            val x |*| yz = split(splittable(a))
            val y |*| z = split(yz)
            (t ** outputS(x) ** outputS(y) ** outputS(z))
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
            val ab |*| cd = split(splittable(x))
            val a |*| b = split(ab)
            val c |*| d = split(cd)
            (t ** ((outputS(a) ** outputS(b)) ** (outputS(c) ** outputS(d))))
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
            val a1 |*| a2 = nt.split(nt.splittable(a))
            val b = merge(mergeable(unnestS(a1)) |*| mergeable(unnestS(a2)))
            (t ** (output(unnestS(a1)) ** output(unnestS(a2))))
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
            val a |*| t = nt.abstractTypeTap(nt.lbl(1))
            val a1 |*| a2 = nt.split(nt.splittable(a))
            val b = merge(mergeable(unnestS(a1)) |*| mergeable(unnestS(a2)))
            (t ** outputM(b))
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
            val a |*| resp = TypeEmitter.makeAbstractType[Done](ti.lbl(2) waitFor start)
            ti.split(a) |*| resp
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
            l0 = OutPort.constant(ti.mkLabel(1))
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
            val a |*| ta = nt.abstractTypeTap(nt.lbl(1))
            val b |*| tb = abstractTypeTap(label(2))
            val a1 |*| a2 = nt.split(nt.splittable(a))
            val c = merge(mergeable(unnestS(a2)) |*| mergeable(b))
            ((outputM(c) ** nt.outputS(a1)) ** (ta ** tb))
              .waitFor(start)
          }
        }
        .via { port =>
          for {
            ts <- expectVal(port)
            ((c, a), (t1, t2)) = ts
            _ <- assertAbstractEquals(c, 2)
            _ <- assertAbstractEquals(a, 2)
            _ <- assertAbstractEquals(t1, 2)
            _ <- assertAbstractEquals(t2, 2)
          } yield ()
        },

      "split two abstract types, merge one from each" -> TestCase
        .interactWith {
          λ { start =>
            val a |*| ta = nt.abstractTypeTap(nt.lbl(1))
            val b |*| tb = nt.abstractTypeTap(nt.lbl(2))
            val a1 |*| a2 = nt.split(nt.splittable(a))
            val b1 |*| b2 = nt.split(nt.splittable(b))
            val c = merge(mergeable(unnestS(a2)) |*| mergeable(unnestS(b2)))
            (outputM(c) ** (nt.outputS(a1) ** nt.outputS(b1)) ** (ta ** tb))
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
            val a1 |*| a2 = nt.split(nt.splittable(a))
            val b1 = unnestS(a1)
            val b2 = unnestS(a2)
            val b = merge(mergeable(b1) |*| mergeable(b2))
            outputM(b) |*| (t waitFor d)
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
            recCall(a |*| b)
              |*| (ta |*| tb.waitFor(start))
          }
        }
        .via { port =>
          val (t, ts) = OutPort.split(port)
          val (ta, tb) = OutPort.split(ts)
          for {
            ab <- expectRight(OutPort.map(t)(tap > isRecCall))
            (a, b) = OutPort.split(ab)
            ta1 <- expectVal(OutPort.map(a)(outputOW))
            tb1 <- expectVal(OutPort.map(b)(outputOW))
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
            val a |*| ta = nt.abstractTypeTap(nt.lbl(1))
            val b |*| tb = abstractTypeTap(label(2))
            val a1 |*| a2 = nt.split(nt.splittable(a))
            pair(recCall(unnestS(a1) |*| b) |*| unnestS(a2))
              |*| (ta |*| tb.waitFor(start))
          }
        }
        .via { port =>
          val (t, ts)  = OutPort.split(port)
          val (ta, tb) = OutPort.split(ts)
          for {
            fa <- expectRight(OutPort.map(t)(tap > isPair))
            (f, a2) = OutPort.split(fa)
            ab <- expectRight(OutPort.map(f)(isRecCall))
            (a1, b) = OutPort.split(ab)

            ta1 = OutPort.map(a1)(outputOW)
            ta2 = OutPort.map(a2)(outputOW)
            tb0 = OutPort.map(b)(outputOW)

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
            val a |*| ta = nnt.abstractTypeTap(nnt.lbl(1))
            val b |*| tb = nnt.abstractTypeTap(nnt.lbl(2))
            val a1 |*| a2 = nnt.split(nnt.splittable(a))
            val b1 |*| b2 = nnt.split(nnt.splittable(b))
            nt.pair(nt.recCall(nn.unnestS(a1) |*| nn.unnestS(b1)) |*| nn.unnestS(a2)) |*| nn.unnestS(b2)
              |*| (ta |*| tb.waitFor(start))
          }
        }
        .via { port =>
          val (t, ts)  = OutPort.split(port)
          val (fa, b2) = OutPort.split(t)
          val (ta, tb) = OutPort.split(ts)
          for {
            fa <- expectRight(OutPort.map(fa)(nt.tap > nt.isPair))
            (f, a2) = OutPort.split(fa)
            ab <- expectRight(OutPort.map(f)(nt.isRecCall))
            (a1, b1) = OutPort.split(ab)

            a = OutPort.map(OutPort.pair(a1, a2))(nested.mergeLower)
            b = OutPort.map(OutPort.pair(b1, OutPort.map(b2)(nt.tap)))(nested.mergeLower)

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
