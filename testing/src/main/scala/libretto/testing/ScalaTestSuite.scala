package libretto.testing

import scala.{:: => NonEmptyList}

/** Test suite where all tests are written using [[ScalaTestKit]] (and thus [[libretto.ScalaDSL]]). */
trait ScalaTestSuite extends TestSuite {
  def testCases(using kit: ScalaTestKit): Tests.Cases[kit.type]

  def testExecutors: NonEmptyList[TestExecutor.Factory[ScalaTestKit]] =
    NonEmptyList(
      TestExecutor.Factory.noOp(ScalaTestExecutor.global),
      Nil
    )

  override def tests: Tests = {
    val (executor :: executors) = testExecutors
    Tests
      .writtenUsing[ScalaTestKit]
      .executedBy(executor, executors: _*)
      .in(testCases)
  }
}
