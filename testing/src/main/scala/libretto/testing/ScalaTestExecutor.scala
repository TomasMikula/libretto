package libretto.testing

import java.util.concurrent.{Executors, ExecutorService, ScheduledExecutorService}
import libretto.{CoreLib, StarterKit}
import scala.concurrent.{Await, Future}
import scala.concurrent.duration._
import scala.util.{Failure, Success, Try}

object ScalaTestExecutor {
  lazy val global: TestExecutor[ScalaTestDsl] =
    new TestExecutor[ScalaTestDsl] {
      val scheduler: ScheduledExecutorService = Executors.newScheduledThreadPool(2)
      val blockingExecutor: ExecutorService   = Executors.newCachedThreadPool()

      val runner =
        StarterKit.runner(blockingExecutor)(scheduler)

      override val testDsl: TestDslImpl.type =
        TestDslImpl

      import testDsl.dsl.{-⚬, Done}

      override def runTestCase(testCase: Done -⚬ testDsl.TestResult): TestResult = {
        val prg =
          testCase > testDsl.resultToScala

        Try {
          Await.result(
            runner.runScala(prg),
            5.seconds,
          )
        } match {
          case Success(r) => r
          case Failure(e) => TestResult.Crash(e)
        }
      }
    }

  private object TestDslImpl extends ScalaTestDsl {
    override val dsl: StarterKit.dsl.type =
      StarterKit.dsl

    private val coreLib = CoreLib(dsl)

    import dsl.{-⚬, |+|, Done, Val, constVal, either, injectL, injectR, mapVal, neglect}
    import coreLib.|+|

    override type TestResult =
      Done |+| Done

    override def success: Done -⚬ TestResult =
      injectL

    override def failure: Done -⚬ TestResult =
      injectR

    override def assertEquals[A](expected: A): Val[A] -⚬ TestResult =
      mapVal[A, Either[Unit, Unit]](a => if (a == expected) Left(()) else Right(()))
        .>( dsl.liftEither )
        .>( |+|.bimap(neglect, neglect) )

    def resultToScala: TestResult -⚬ Val[libretto.testing.TestResult] =
      either(
        constVal(libretto.testing.TestResult.Success),
        constVal(libretto.testing.TestResult.Failure("KO"))
      )
  }
}
