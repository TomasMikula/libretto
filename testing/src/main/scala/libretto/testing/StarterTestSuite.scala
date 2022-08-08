package libretto.testing

/** Test suite where all tests are written using [[StarterTestKit]]. */
trait StarterTestSuite extends TestSuite[StarterTestKit] {
  override def testExecutors: List[TestExecutor.Factory[StarterTestKit]] =
    List(
      TestExecutor.Factory.noOp(StarterTestExecutor.global),
    )
}
