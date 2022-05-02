package libretto.testing


trait TestExecutor[TDSL <: TestDsl] {
  val testDsl: TDSL

  import testDsl.dsl._

  def runTestCase(testCase: Done -⚬ testDsl.TestResult): TestResult
}
