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
    import kit.{Outcome, expectVal}
    import Outcome.{assertEquals, assertRight, failure, success}

    import TypeInference.{Labels, Tools, Type}
    import Labels.Label

    val tools = Tools.groundInstance
    import tools.{abstractTypeTap, close, merge, nested, newAbstractType, output, split, unnest}

    def label(n: Int)(using
      SourcePos,
      LambdaContext,
    ): $[Label] =
      constant(tools.label(AbstractTypeLabel(n)))

    def assertAbstract(t: Type): Outcome[AbstractTypeLabel] =
      t.value match {
        case gte.AbstractType(label) => assertRight(label)
        case other                   => failure(s"Expected abstract type, got $other")
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
            l <- assertAbstract(t)
            _ <- assertEquals(l.value, 1)
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
            l <- assertAbstract(t)
            _ <- assertEquals(l.value, 1)
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
            l <- assertAbstract(t)
            _ <- assertEquals(l.value, 1)
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
            l <- assertAbstract(t)
            _ <- assertEquals(l.value, 1)
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
            _ <- assertEquals(vt.value, 1)
            _ <- assertEquals(vx.value, 1)
            _ <- assertEquals(vy.value, 1)
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
            vt <- assertAbstract(t)
            vb <- assertAbstract(b)
            _ <- assertEquals(vt.value, 1)
            _ <- assertEquals(vb.value, 1)
          } yield ()
        },

      "merge abstract types (one of them newAbstractType)" -> TestCase
        .interactWith {
          λ { start =>
            val a |*| t1 |*| b = newAbstractType(label(1))
            val c |*| t2       = abstractTypeTap(label(2))
            val t = merge(b |*| c)
            ((output(t) ** output(a)) ** (t1 ** t2))
              .waitFor(start)
          }
        }
        .via { port =>
          for {
            ts <- expectVal(port)
            ((t, a), (t1, t2)) = ts
            vt <- assertAbstract(t)
            va <- assertAbstract(a)
            v1 <- assertAbstract(t1)
            v2 <- assertAbstract(t2)
            _ <- assertEquals(vt.value, 1)
            _ <- assertEquals(va.value, 1)
            _ <- assertEquals(v1.value, 1)
            _ <- assertEquals(v2.value, 1)
          } yield ()
        },

      "merge abstract types (both newAbstractType)" -> TestCase
        .interactWith {
          val prg: Done -⚬ Val[Type] = λ { start =>
            val a |*| t1 |*| b = newAbstractType(label(1))
            val c |*| t2 |*| d = newAbstractType(label(2))
            val t = merge(b |*| c)
            output(t)
              .waitFor(start)
              .waitFor(neglect(t1))
              .waitFor(neglect(t2))
              .waitFor(close(a))
              .waitFor(close(d))
          }
          prg
        }
        .via { port =>
          for {
            t <- expectVal(port)
            l <- assertAbstract(t)
            _ <- assertEquals(l.value, 1)
          } yield ()
        },
    )
  }
}
