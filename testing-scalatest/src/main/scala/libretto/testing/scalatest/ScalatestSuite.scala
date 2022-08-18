package libretto.testing.scalatest

import libretto.testing.{TestCase, TestExecutor, TestKit, TestResult}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.BeforeAndAfterAll

abstract class ScalatestSuite[Kit <: TestKit]
extends AnyFunSuite
   with BeforeAndAfterAll
   with libretto.testing.TestSuite[Kit]
{
  private class FactoryWithExecutor[F <: TestExecutor.Factory[_]](
    val factory: F,
  ) {
    var executor: Option[factory.ExecutorResource] = None

    def init(): Unit =
      executor = Some(factory.create())

    def destroy(): Unit =
      executor.foreach(factory.shutdown(_))

    def getExecutor(): TestExecutor[factory.testKit.type] =
      executor.map(factory.access(_)).getOrElse {
        throw new IllegalStateException(s"TestExecutor ${factory.name} not  initialzed.")
      }
  }

  private object FactoryWithExecutor {
    def apply(factory: TestExecutor.Factory[_]): FactoryWithExecutor[factory.type] =
      new FactoryWithExecutor(factory)
  }

  private var executors: List[FactoryWithExecutor[_]] = Nil

  private def registerTests(): Unit = {
    this.executors =
      this.testExecutors.map { factory =>
        val res = FactoryWithExecutor(factory)
        registerTests(
          factory.testKit,
          factory.name,
          res.getExecutor,
          prefix = "",
          this.testCases(using factory.testKit),
        )
        res
      }
  }

  private def registerTests(
    testKit: TestKit,
    testExecutorName: String,
    testExecutor: () => TestExecutor[testKit.type],
    prefix: String,
    cases: List[(String, TestCase[testKit.type])],
  ): Unit = {
    for {
      (testName, testCase) <- cases
    } {
      testCase match {
        case c: TestCase.Single[testKit.type] =>
          val fullName = s"$prefix$testName (executed by $testExecutorName)"
          def handleTestResult(r: TestResult[Unit]): Unit =
            r match {
              case TestResult.Success(_) =>
                // do nothing
              case TestResult.Failure(msg, pos, e) =>
                val message = s"$msg (at ${pos.path}:${pos.line})"
                e match {
                  case Some(e) => fail(message, e)
                  case None    => fail(message)
                }
              case TestResult.Crash(e) =>
                fail(s"Crashed with ${e.getClass.getCanonicalName}: ${e.getMessage}", e)
            }
          c match {
            case c: TestCase.SingleProgram[testKit.type] =>
              test(fullName) {
                handleTestResult(
                  testExecutor()
                    .runTestCase(c.body, c.params, c.conductor(_, _), c.postStop)
                )
              }
            case c: TestCase.OutcomeOnly[testKit.type] =>
              test(fullName) {
                handleTestResult(
                  testExecutor().runTestCase(c.body)
                )
              }
          }
        case TestCase.Multiple(cases) =>
          registerTests(testKit, testExecutorName, testExecutor, s"$prefix$testName.", cases)
      }
    }
  }

  override protected def beforeAll(): Unit =
    for (f <- executors) {
      f.init()
    }

  override protected def afterAll(): Unit =
    for (f <- executors) {
      f.destroy()
    }

  registerTests()
}
