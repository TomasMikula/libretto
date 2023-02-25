package libretto.testing.scalatest

import libretto.testing.{TestCase, TestExecutor, TestKit, TestResult}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.BeforeAndAfterAll
import org.scalatest.Checkpoints.Checkpoint

abstract class ScalatestSuite[Kit <: TestKit]
extends AnyFunSuite
   with BeforeAndAfterAll
   with libretto.testing.TestSuite[Kit]
{
  private class FactoryWithExecutor[F <: TestExecutor.Factory[?]](
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
    def apply(factory: TestExecutor.Factory[?]): FactoryWithExecutor[factory.type] =
      new FactoryWithExecutor(factory)
  }

  private var executors: List[FactoryWithExecutor[?]] = Nil

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
          isPending = false,
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
    isPending: Boolean,
  ): Unit = {
    def registerTest(
      testName: String,
      testCase: TestCase[testKit.type],
      isPending: Boolean,
    ): Unit =
      testCase match {
        case c: TestCase.Single[testKit.type] =>
          val fullName = s"$prefix$testName (executed by $testExecutorName)"
          def handleTestResult(r: TestResult[Unit]): Unit =
            r match {
              case TestResult.Success(_) =>
                if (isPending) {
                  fail(s"Pending test succeeded. You should remove the pending qualifier.")
                } else {
                  // do nothing
                }
              case TestResult.Failures(es) =>
                if (isPending) {
                  pending
                } else {
                  import TestResult.Failure.{Crash, Failed, TimedOut}
                  val cp = new Checkpoint()
                  es.foreach { e =>
                    cp {
                      e match {
                        case Failed(msg, pos, e) =>
                          val message = s"$msg (at ${pos.path}:${pos.line})"
                          e match {
                            case Some(e) => fail(message, e)
                            case None    => fail(message)
                          }
                        case Crash(e) =>
                          fail(s"Crashed with ${e.getClass.getCanonicalName}: ${e.getMessage}", e)
                        case TimedOut(d) =>
                          fail(s"Timed out after $d")
                      }
                    }
                  }
                  cp.reportAll()
                }
            }
          c match {
            case c: TestCase.SingleProgram[testKit.type] =>
              test(fullName) {
                handleTestResult(
                  testExecutor()
                    .execpAndCheck(c.body, c.params, c.conductor(_, _), c.postStop, c.timeout)
                )
              }
            case c: TestCase.Pure[testKit.type] =>
              test(fullName) {
                handleTestResult(
                  testExecutor().check(c.body, c.timeout)
                )
              }
          }
        case TestCase.Multiple(cases) =>
          registerTests(testKit, testExecutorName, testExecutor, s"$prefix$testName.", cases, isPending)
        case TestCase.Pending(testCase) =>
          registerTest(testName, testCase, isPending = true)
      }

    for {
      (testName, testCase) <- cases
    } {
      registerTest(testName, testCase, isPending)
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
