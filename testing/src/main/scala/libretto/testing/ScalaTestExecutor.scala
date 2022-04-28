package libretto.testing

import java.util.concurrent.{Executors, ExecutorService, ScheduledExecutorService}
import libretto.StarterKit
import scala.concurrent.{Await, Future}
import scala.concurrent.duration._

object ScalaTestExecutor {
  lazy val global: TestExecutor[ScalaTestDsl] =
    new TestExecutor[ScalaTestDsl] {
      val scheduler: ScheduledExecutorService = Executors.newScheduledThreadPool(2)
      val blockingExecutor: ExecutorService   = Executors.newCachedThreadPool()

      val runner =
        StarterKit.runner(blockingExecutor)(scheduler)

      override def runTestCase(testCase: (tdsl: ScalaTestDsl) ?=> tdsl.TestCase): TestResult = {
        val prg =
          testCase(using testDsl) > testDsl.resultToScala

        Await.result(
          runner.runScala(prg),
          5.seconds,
        )
      }
    }

  private object testDsl extends ScalaTestDsl {
    override val dsl: StarterKit.dsl.type =
      StarterKit.dsl

    import dsl.{-⚬, |+|, Done, Val, constVal, either, injectL, injectR}

    override type TestResult =
      Done |+| Done

    override def success: Done -⚬ TestResult =
      injectL

    override def failure: Done -⚬ TestResult =
      injectR

    def resultToScala: TestResult -⚬ Val[libretto.testing.TestResult] =
      either(
        constVal(libretto.testing.TestResult.Success),
        constVal(libretto.testing.TestResult.Failure)
      )
  }
}
