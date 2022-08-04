package libretto.testing

import java.util.concurrent.{Executors, ExecutorService, ScheduledExecutorService}
import libretto.{CoreLib, Monad, ScalaBridge, ScalaExecutor, ScalaDSL, StarterKit}
import libretto.scalasource.{Position => SourcePos}
import libretto.util.{Async, Monad => ScalaMonad}
import libretto.util.Monad.syntax._
import scala.concurrent.{Await, ExecutionContext, Future}
import scala.concurrent.duration._
import scala.util.{Failure, Success, Try}

object ScalaTestExecutor {

  class ScalaTestKitFromBridge[DSL <: ScalaDSL, Bridge <: ScalaBridge.Of[DSL]](
    val dsl0: DSL,
    val bridge: Bridge & ScalaBridge.Of[dsl0.type],
  ) extends ScalaTestKit {
      override val dsl: bridge.dsl.type = bridge.dsl
      override val probes: bridge.type = bridge
      import dsl._
      import probes.Execution

      override type Assertion[A] = Val[String] |+| A

      private val coreLib = CoreLib(this.dsl)
      import coreLib.{Monad => _, _}

      override def success[A]: A -⚬ Assertion[A] =
        injectR

      override def failure[A]: Done -⚬ Assertion[A] =
        failure("Failed")

      override def failure[A](msg: String): Done -⚬ Assertion[A] =
        constVal(msg) > injectL

      override def monadAssertion: Monad[-⚬, Assertion] =
        |+|.right[Val[String]]

      override def extractOutcome(using exn: Execution, pos: SourcePos)(
        outPort: exn.OutPort[Assertion[Done]],
      ): Outcome[Unit] = {
        import TestResult.{Crash, Success, Failure}
        Outcome.asyncTestResult(
          exn.OutPort
            .awaitEither[Val[String], Done](outPort)
            .flatMap {
              case Left(e) =>
                Async.now(Crash(e))
              case Right(Left(msg)) =>
                exn.OutPort.awaitVal(msg).map {
                  case Left(e)    => Crash(e)
                  case Right(msg) => Failure(msg, pos)
                }
              case Right(Right(d)) =>
                exn.OutPort.awaitDone(d).map {
                  case Left(e)   => Crash(e)
                  case Right(()) => Success(())
                }
            }
        )
      }
  }

  def fromExecutor(
    dsl: ScalaDSL,
    exec: ScalaExecutor.OfDsl[dsl.type],
  ): TestExecutor[ScalaTestKit] =
    new TestExecutor[ScalaTestKit] {
      override val name: String =
        ScalaTestExecutor.getClass.getCanonicalName

      override val testKit: ScalaTestKitFromBridge[dsl.type, exec.bridge.type] =
        new ScalaTestKitFromBridge[dsl.type, exec.bridge.type](dsl, exec.bridge)

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
  ): TestExecutor[ScalaTestKit] = {
    val executor0: libretto.ScalaExecutor.OfDsl[StarterKit.dsl.type] =
      StarterKit.executor(blockingExecutor)(scheduler)

    given monadFuture: ScalaMonad[Future] =
      ScalaMonad.monadFuture(using ExecutionContext.fromExecutor(scheduler))

    fromExecutor(StarterKit.dsl, executor0)
  }

  lazy val global: TestExecutor[ScalaTestKit] =
    fromJavaExecutors(
      scheduler        = Executors.newScheduledThreadPool(4),
      blockingExecutor = Executors.newCachedThreadPool(),
    )
}
