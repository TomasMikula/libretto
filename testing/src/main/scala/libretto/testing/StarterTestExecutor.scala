package libretto.testing

import java.util.concurrent.{Executors, ExecutorService, ScheduledExecutorService}
import libretto.{CoreLib, Monad, ScalaBridge, ScalaExecutor, ScalaDSL, StarterKit}
import libretto.util.{Monad => ScalaMonad}
import libretto.util.Monad.syntax._
import scala.concurrent.{Await, ExecutionContext, Future}
import scala.concurrent.duration._
import scala.util.{Failure, Success, Try}

object StarterTestExecutor {

  private class StarterTestKitFromBridge[Bridge <: ScalaBridge.Of[StarterKit.dsl.type]](
    bridge: Bridge,
  )(using
    ScalaMonad[Future],
  ) extends ScalaTestExecutor.ScalaTestKitFromBridge[StarterKit.dsl.type, Bridge](StarterKit.dsl, bridge)
       with StarterTestKit

  def fromExecutor(
    exec: ScalaExecutor.OfDsl[StarterKit.dsl.type],
  )(using
    ScalaMonad[Future],
  ): TestExecutor[StarterTestKit] =
    new TestExecutor[StarterTestKit] {
      override val name: String =
        StarterTestExecutor.getClass.getCanonicalName

      override val testKit: StarterTestKitFromBridge[exec.bridge.type] =
        new StarterTestKitFromBridge(exec.bridge)

      import testKit.Outcome
      import testKit.dsl._
      import testKit.probes.Execution

      override def runTestCase[O, X](
        body: Done -⚬ O,
        conduct: (exn: Execution) ?=> exn.OutPort[O] => Outcome[X],
        postStop: X => Outcome[Unit],
      ): TestResult[Unit] =
        TestExecutor
          .usingExecutor(exec)
          .runTestCase[O, X](
            body,
            conduct andThen Outcome.toAsyncTestResult,
            postStop andThen Outcome.toAsyncTestResult,
          )

      override def runTestCase(body: () => Outcome[Unit]): TestResult[Unit] =
        TestExecutor
          .usingExecutor(exec)
          .runTestCase(() => Outcome.toAsyncTestResult(body()))
    }

  def fromJavaExecutors(
    scheduler: ScheduledExecutorService,
    blockingExecutor: ExecutorService,
  ): TestExecutor[StarterTestKit] = {
    val executor0: libretto.ScalaExecutor.OfDsl[StarterKit.dsl.type] =
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
