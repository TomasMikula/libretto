package libretto.testing

import org.scalatest.funsuite.AnyFunSuite

abstract class ScalatestSuite extends AnyFunSuite {
  def tests: Tests

  private def registerTests(): Unit = {
    val tests = this.tests
    for {
      testExecutor <- tests.testExecutors
      (testName, testCase) <- tests.testCases(using testExecutor.testDsl)
    } {
      test(testName) {
        testCase.resultTrans(testExecutor.runTestCase(testCase.body)) match {
          case TestResult.Success =>
            // do nothing
          case TestResult.Failure(msg) =>
            fail(msg)
          case TestResult.Crash(e) =>
            fail(e)
        }
      }
    }
  }

  registerTests()
}
