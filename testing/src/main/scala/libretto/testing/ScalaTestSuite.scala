package libretto.testing

/** Test suite where all tests are written using [[ScalaTestKit]] (and thus [[libretto.ScalaDSL]]). */
trait ScalaTestSuite extends TestSuite[ScalaTestKit] {
  override def testExecutors: List[TestExecutor.Factory[ScalaTestKit]] =
    List(
      ScalaTestExecutor.defaultFactory,
    )
}
