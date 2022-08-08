package libretto.testing

/** Test suite where all tests are written using [[ScalaTestKit]] (and thus [[libretto.ScalaDSL]]). */
trait ScalaTestSuite extends TestSuite {
  def testCases(using kit: ScalaTestKit): List[(String, TestCase[kit.type])]

  def testExecutors: List[TestExecutor.Factory[ScalaTestKit]] =
    List(
      TestExecutor.Factory.noOp(ScalaTestExecutor.global),
    )

  override def tests: Tests =
    Tests
      .writtenUsing[ScalaTestKit]
      .executedBy(testExecutors: _*)
      .in(testCases)
}
