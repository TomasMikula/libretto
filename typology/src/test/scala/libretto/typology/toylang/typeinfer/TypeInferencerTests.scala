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
    import Outcome.{failure, success}

    import TypeInference.{Labels, Tools, Type}
    import Labels.Label

    val tools = Tools.groundInstance
    import tools.{newAbstractType}

    def label(n: Int)(using
      SourcePos,
      LambdaContext,
    ): $[Label] =
      constant(tools.label(AbstractTypeLabel(n)))

    List(
      "newAbstractType" -> TestCase
        .interactWith {
          val prg: Done -⚬ Val[Type] = λ { d =>
            val (x1 |*| t |*| x2) = tools.newAbstractType(label(1))
            t
              .waitFor(d)
              .waitFor(tools.close(x1))
              .waitFor(tools.close(x2))
          }
          prg
        }
        .via { port =>
          for {
            t <- expectVal(port)
            l <- t.value match
              case gte.AbstractType(label) => success(label)
              case other                   => failure(s"Expected abstract type, got $other")
            l <- Outcome.assertRight(l)
            _ <- Outcome.assertEquals(l.value, 1)
          } yield ()
        }
    )
  }
}
