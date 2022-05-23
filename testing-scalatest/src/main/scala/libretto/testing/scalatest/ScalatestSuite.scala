package libretto.testing.scalatest

import libretto.testing.{TestCase, TestExecutor, TestKit, TestResult, Tests}
import org.scalatest.funsuite.AnyFunSuite

abstract class ScalatestSuite extends AnyFunSuite {
  def tests: Tests

  private def registerTests(): Unit = {
    val tests = this.tests
    for {
      testExecutor <- tests.testExecutors
    } {
      registerTests[tests.Kit](testExecutor, prefix = "", tests.testCases(using testExecutor.testKit))
    }
  }

  private def registerTests[TK <: TestKit](
    testExecutor: TestExecutor[TK],
    prefix: String,
    cases: List[(String, TestCase[testExecutor.testKit.type])],
  ): Unit = {
    for {
      (testName, testCase) <- cases
    } {
      testCase match {
        case c: TestCase.Single[testExecutor.testKit.type] =>
          test(s"$prefix$testName (executed by ${testExecutor.name})") {
            testExecutor.runTestCase(c.body, c.conductor, c.postStop) match {
              case TestResult.Success(_) =>
                // do nothing
              case TestResult.Failure(msg) =>
                fail(msg)
              case TestResult.Crash(e) =>
                fail(s"Crashed with ${e.getClass.getCanonicalName}: ${e.getMessage}", e)
            }
          }
        case TestCase.Multiple(cases) =>
          registerTests(testExecutor, s"$prefix$testName.", cases)
      }
    }
  }

  registerTests()
}
