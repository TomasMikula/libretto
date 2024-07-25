package libretto.examples.interactionNets.unaryArithmetic

import libretto.examples.interactionNets.unaryArithmetic.*
import libretto.scaletto.StarterKit.*
import libretto.testing.scalatest.scaletto.ScalatestStarterTestSuite
import libretto.testing.scaletto.StarterTestKit
import libretto.testing.TestCase

class UnaryArithmeticTests extends ScalatestStarterTestSuite {

  private def testOp(x: Int, y: Int)(expected: Int)(op: (Wire |*| Wire) -⚬ Wire)(using kit: StarterTestKit): TestCase[kit.type] =
    import kit.Outcome.assertEquals

    TestCase.awaitVal {
      val prg: Done -⚬ Val[Result] =
        λ { start =>
          val a = constant(liftInt(x))
          val b = constant(liftInt(y))
          val out1 |*| out2 = constant(newWire)
          readResult(out2)
            .waitFor(start)
            .alsoElim(connect(a |*| op(b |*| out1)))
        }

      prg
    }.checkThat {
      assertEquals(_, Result.liftInt(expected))
    }

  private def testAddition(x: Int, y: Int)(using kit: StarterTestKit): TestCase[kit.type] =
    testOp(x, y)(x + y)(plus)

  private def testMultiplication(x: Int, y: Int)(using kit: StarterTestKit): TestCase[kit.type] =
    testOp(x, y)(x * y)(times)

  override def testCases(using kit: StarterTestKit): List[(String, TestCase[kit.type])] =
    List(
      "2 + 3"     -> testAddition(2, 3),
      "100 + 200" -> testAddition(100, 200),
      "2 * 3"     -> testMultiplication(2, 3),
      "7 * 19"    -> testMultiplication(7, 19),
    )
}
