package libretto.testing

import java.util.concurrent.{Executors, ExecutorService, ScheduledExecutorService}
import libretto.{CoreLib, ScalaBridge, ScalaExecutor, ScalaDSL, StarterKit}
import libretto.util.Monad
import libretto.util.Monad.syntax._
import scala.concurrent.{Await, ExecutionContext, Future}
import scala.concurrent.duration._
import scala.util.{Failure, Success, Try}

object ScalaTestExecutor {

  private trait ScalaTestDslFromExecutor[F0[_]: Monad, DSL <: ScalaDSL, Exec <: ScalaExecutor.Of[DSL, F0]](
    val dsl0: DSL,
    val exec: Exec & ScalaExecutor.Of[dsl0.type, F0],
  ) extends ScalaTestDsl {
      override type F[A] = F0[A]
      override val dsl: exec.dsl.type = exec.dsl
      override val probes: exec.type = exec
      import dsl._

      override type TestResult = Val[String] |+| Done

      private val coreLib = CoreLib(this.dsl)
      import coreLib._

      override def F: libretto.util.Monad[F0] =
        summon[libretto.util.Monad[F0]]

      override def success: Done -⚬ TestResult =
        injectR

      override def failure: Done -⚬ TestResult =
        constVal("Failed") > injectL

      override def extractTestResult(outPort: exec.OutPort[TestResult]): F0[libretto.testing.TestResult] = {
        import libretto.testing.TestResult.{Crash, Success, Failure}
        exec
          .awaitEither[Val[String], Done](outPort)
          .flatMap {
            case Left(e) =>
              F.pure(Crash(e))
            case Right(Left(msg)) =>
              exec.awaitVal(msg).map {
                case Left(e)    => Crash(e)
                case Right(msg) => Failure(msg)
              }
            case Right(Right(d)) =>
              exec.awaitDone(d).map {
                case Left(e)   => Crash(e)
                case Right(()) => Success
              }
          }
      }
  }

  def fromExecutor[F0[_]: Monad](dsl: ScalaDSL, exec: ScalaExecutor.Of[dsl.type, F0]): TestExecutor[ScalaTestDsl] =
    new TestExecutor[ScalaTestDsl] {
      override val name: String =
        ScalaTestExecutor.getClass.getCanonicalName

      override val testDsl: ScalaTestDslFromExecutor[F0, dsl.type, exec.type] =
        new ScalaTestDslFromExecutor[F0, dsl.type, exec.type](dsl, exec) {}

      import testDsl.dsl._
      import testDsl.probes.OutPort

      override def runTestCase[O](
        body: Done -⚬ O,
        conduct: OutPort[O] => F0[TestResult],
      ): TestResult =
        TestExecutor.usingExecutor(exec).runTestCase[O](body, conduct)
    }

  lazy val global: TestExecutor[ScalaTestDsl] = {
    val scheduler: ScheduledExecutorService = Executors.newScheduledThreadPool(2)
    val blockingExecutor: ExecutorService   = Executors.newCachedThreadPool()

    val executor0: libretto.ScalaExecutor.Of[StarterKit.dsl.type, Future] =
      StarterKit.executor(blockingExecutor)(scheduler)

    given monadFuture: Monad[Future] =
      Monad.monadFuture(using ExecutionContext.fromExecutor(scheduler))

    fromExecutor(StarterKit.dsl, executor0)
  }
}
