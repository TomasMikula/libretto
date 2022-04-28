package libretto.testing

trait TestExecutor[TDSL <: TestDsl] {
  def runTestCase(testCase: (tdsl: TDSL) ?=> tdsl.TestCase): TestResult
}
