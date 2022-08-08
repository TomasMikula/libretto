package libretto.testing

/** Test suite where all tests are written using [[StarterTestKit]]. */
trait StarterTestSuite extends TestSuite {
  def testCases(using kit: StarterTestKit): List[(String, TestCase[kit.type])]

  def testExecutors: List[TestExecutor.Factory[StarterTestKit]] =
    List(
      TestExecutor.Factory.noOp(StarterTestExecutor.global),
    )

  override def tests: Tests =
    Tests
      .writtenUsing[StarterTestKit]
      .executedBy(testExecutors: _*)
      .in(testCases)
}
