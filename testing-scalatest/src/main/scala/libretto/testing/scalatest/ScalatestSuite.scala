package libretto.testing.scalatest

import libretto.testing.{TestCase, TestExecutor, TestKit, TestResult, Tests}
import org.scalatest.funsuite.AnyFunSuite

abstract class ScalatestSuite extends AnyFunSuite with libretto.testing.TestSuite {

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
          val fullName = s"$prefix$testName (executed by ${testExecutor.name})"
          def handleTestResult(r: TestResult[Unit]): Unit =
            r match {
              case TestResult.Success(_) =>
                // do nothing
              case TestResult.Failure(msg, pos) =>
                fail(s"$msg (at ${pos.file}:${pos.line})")
              case TestResult.Crash(e) =>
                fail(s"Crashed with ${e.getClass.getCanonicalName}: ${e.getMessage}", e)
            }
          c match {
            case c: TestCase.SingleProgram[testExecutor.testKit.type] =>
              test(fullName) {
                handleTestResult(
                  testExecutor.runTestCase(c.body, c.conductor(_), c.postStop)
                )
              }
            case c: TestCase.OutcomeOnly[testExecutor.testKit.type] =>
              test(fullName) {
                handleTestResult(
                  testExecutor.runTestCase(c.body)
                )
              }
          }
        case TestCase.Multiple(cases) =>
          registerTests(testExecutor, s"$prefix$testName.", cases)
      }
    }
  }

  registerTests()
}
