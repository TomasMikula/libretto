package libretto.testing

import java.util.concurrent.{Executors, ExecutorService, ScheduledExecutorService}
import libretto.{CoreLib, Monad, ScalaBridge, ScalaExecutor, ScalaDSL, StarterKit}
import libretto.util.{Monad => ScalaMonad}
import libretto.util.Monad.syntax._
import scala.concurrent.{Await, ExecutionContext, Future}
import scala.concurrent.duration._
import scala.util.{Failure, Success, Try}

object StarterTestExecutor {

  private class StarterTestKitFromExecutor[Exec <: ScalaExecutor.Of[StarterKit.dsl.type, Future]](
    exec: Exec,
  )(using
    ScalaMonad[Future],
  ) extends ScalaTestExecutor.ScalaTestKitFromExecutor[Future, StarterKit.dsl.type, Exec](StarterKit.dsl, exec) with StarterTestKit

  def fromExecutor(
    exec: ScalaExecutor.Of[StarterKit.dsl.type, Future],
  )(using
    ScalaMonad[Future],
  ): TestExecutor[StarterTestKit] =
    new TestExecutor[StarterTestKit] {
      override val name: String =
        StarterTestExecutor.getClass.getCanonicalName

      override val testKit: StarterTestKitFromExecutor[exec.type] =
        new StarterTestKitFromExecutor(exec)

      import testKit.Outcome
      import testKit.dsl._
      import testKit.probes.OutPort

      override def runTestCase[O, X](
        body: Done -⚬ O,
        conduct: OutPort[O] => Outcome[X],
        postStop: X => Outcome[Unit],
      ): TestResult[Unit] =
        TestExecutor
          .usingExecutor(exec)
          .runTestCase[O, X](
            body,
            conduct andThen Outcome.unwrap,
            postStop andThen Outcome.unwrap,
          )
    }

  def fromJavaExecutors(
    scheduler: ScheduledExecutorService,
    blockingExecutor: ExecutorService,
  ): TestExecutor[StarterTestKit] = {
    val executor0: libretto.ScalaExecutor.Of[StarterKit.dsl.type, Future] =
      StarterKit.executor(blockingExecutor)(scheduler)

    given monadFuture: ScalaMonad[Future] =
      ScalaMonad.monadFuture(using ExecutionContext.fromExecutor(scheduler))

    fromExecutor(executor0)
  }

  lazy val global: TestExecutor[StarterTestKit] =
    fromJavaExecutors(
      scheduler        = Executors.newScheduledThreadPool(4),
      blockingExecutor = Executors.newCachedThreadPool(),
    )
}
