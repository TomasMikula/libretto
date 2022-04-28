package libretto.testing

import org.scalatest.funsuite.AnyFunSuite

abstract class ScalatestSuite extends AnyFunSuite {
  def tests: Tests

  private def registerTests(): Unit = {
    val tests = this.tests
    for {
      testExecutor <- tests.testExecutors
      (testName, testCase) <- tests.testCases
    } {
      test(testName) {
        testExecutor.runTestCase(testCase) match {
          case TestResult.Success =>
            // do nothing
          case TestResult.Failure =>
            fail()
        }
      }
    }
  }

  registerTests()
}
