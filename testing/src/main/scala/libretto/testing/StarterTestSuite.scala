package libretto.testing

import scala.{:: => NonEmptyList}

/** Test suite where all tests are written using [[StarterTestKit]]. */
trait StarterTestSuite extends TestSuite {
  def testCases(using kit: StarterTestKit): Tests.Cases[kit.type]

  def testExecutors: NonEmptyList[TestExecutor.Factory[StarterTestKit]] =
    NonEmptyList(
      TestExecutor.Factory.noOp(StarterTestExecutor.global),
      Nil
    )

  override def tests: Tests = {
    val (executor :: executors) = testExecutors
    Tests
      .writtenUsing[StarterTestKit]
      .executedBy(executor, executors: _*)
      .in(testCases)
  }
}
