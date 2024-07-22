package libretto.testing

trait TestSuite[Kit <: TestKit] {
  def testExecutors: List[TestExecutor.Factory[Kit]]

  def testCases(using kit: Kit): List[(String, TestCase[kit.type])]
}
