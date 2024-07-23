package libretto.testing.scaletto

import java.util.concurrent.{Executors, ExecutorService, ScheduledExecutorService}
import libretto.CoreLib
import libretto.cats.Monad
import libretto.exec.ExecutionParams
import libretto.lambda.util.{Exists, SourcePos, TypeEq}
import libretto.lambda.util.TypeEq.Refl
import libretto.scaletto.{Scaletto, ScalettoBridge, ScalettoExecutor, StarterKit}
import libretto.testing.{ManualClock, TestExecutor, TestResult}
import libretto.util.Async
import scala.concurrent.duration.FiniteDuration

object ScalettoTestExecutor {

  class ScalettoTestKitFromBridge[DSL <: Scaletto, Bridge <: ScalettoBridge.Of[DSL]](
    val dsl0: DSL,
    val bridge0: Bridge & ScalettoBridge.Of[dsl0.type],
  ) extends ScalettoTestKit {
      override type Dsl = bridge.dsl.type

      override val dsl: bridge0.dsl.type = bridge0.dsl
      override val bridge: bridge0.type = bridge0
      import dsl.*
      import bridge.Execution

      override type Assertion[A] = Val[String] |+| A

      override type ExecutionParam[A] = ScalettoTestExecutor.ExecutionParam[A]

      override def manualClockParam: ExecutionParam[ManualClock] =
        ExecutionParam.ManualClockParam

      private val coreLib = CoreLib(this.dsl)
      import coreLib.{Monad as _, *}

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
        import TestResult.{crash, success as succeed, failed as fail}
        import bridge.*
        Outcome.asyncTestResult(
          outPort
            .awaitEither()
            .flatMap {
              case Left(e) =>
                Async.now(crash(e))
              case Right(Left(msg)) =>
                msg.awaitVal().map {
                  case Left(e)    => crash(e)
                  case Right(msg) => fail(using pos)(msg)
                }
              case Right(Right(d)) =>
                d.awaitDone().map {
                  case Left(e)   => crash(e)
                  case Right(()) => succeed(())
                }
            }
        )
      }
  }

  sealed trait ExecutionParam[A]

  object ExecutionParam {
    case object ManualClockParam extends ExecutionParam[ManualClock]

    def adapt[A, P[_]](p: ExecutionParams[ExecutionParam, A])(
      sp: libretto.util.Scheduler => P[Unit],
    ): Exists[[X] =>> (ExecutionParams[P, X], X => A)] =
      p.adapt { [X] => (x: ExecutionParam[X]) =>
        x match {
          case ManualClockParam =>
            val (clock, scheduler) = ManualClock.scheduler()
            Exists((sp(scheduler), _ => clock))
        }
      }
  }

  def fromExecutor(
    exec: ScalettoExecutor,
  ): TestExecutor[ScalettoTestKit.Of[exec.dsl.type]] = {
    val kit = ScalettoTestKitFromBridge[exec.dsl.type, exec.bridge.type](exec.dsl, exec.bridge)
    fromKitAndExecutor(kit, exec)
  }

  def fromKitAndExecutor(
    kit: ScalettoTestKit { type ExecutionParam[A] = ScalettoTestExecutor.ExecutionParam[A] },
    exr: ScalettoExecutor.Of[kit.dsl.type, kit.bridge.type],
  ): TestExecutor[kit.type] =
    new TestExecutor[kit.type] {
      override val name: String =
        ScalettoTestExecutor.getClass.getCanonicalName

      override val testKit: kit.type = kit

      import testKit.{ExecutionParams, Outcome}
      import testKit.dsl.*
      import testKit.bridge.Execution

      override def execpAndCheck[O, P, Y](
        body: Done -⚬ O,
        params: ExecutionParams[P],
        conduct: (exn: Execution) ?=> (exn.OutPort[O], P) => Outcome[Y],
        postStop: Y => Outcome[Unit],
        timeout: FiniteDuration,
      ): TestResult[Unit] = {
        val p: Exists[[X] =>> (libretto.exec.ExecutionParams[exr.ExecutionParam, X], X => P)] =
          ScalettoTestExecutor.ExecutionParam.adapt(params)(exr.schedulerParam)

        TestExecutor
          .usingExecutor(exr)
          .runTestCase[O, p.T, Y](
            body,
            p.value._1,
            (port, x) => Outcome.toAsyncTestResult(conduct(port, p.value._2(x))),
            postStop andThen Outcome.toAsyncTestResult,
            timeout,
          )
      }

      override def check(
        body: () => Outcome[Unit],
        timeout: FiniteDuration,
      ): TestResult[Unit] =
        TestExecutor
          .usingExecutor(exr)
          .runTestCase(() => Outcome.toAsyncTestResult(body()), timeout)
    }

  def fromJavaExecutors(
    scheduler: ScheduledExecutorService,
    blockingExecutor: ExecutorService,
  ): TestExecutor[ScalettoTestKit] = {
    val executor0: ScalettoExecutor.OfDsl[StarterKit.dsl.type] =
      StarterKit.executor(blockingExecutor)(scheduler)

    fromExecutor(executor0)
  }

  def defaultFactory(
    ef: ScalettoExecutor.Factory,
  ): TestExecutor.Factory[ScalettoTestKit.Of[ef.dsl.type]] =
    new TestExecutor.Factory[ScalettoTestKit.Of[ef.dsl.type]] {
      override val testKit: ScalettoTestKitFromBridge[ef.dsl.type, ef.bridge.type] =
        new ScalettoTestKitFromBridge(ef.dsl, ef.bridge)

      override def name: String =
        s"ScalettoTestExecutor.defaultFactory(${ef.name})"

      override type ExecutorResource = (ef.ExecutorResource, TestExecutor[testKit.type])

      override def access(r: ExecutorResource): TestExecutor[testKit.type] =
        r._2

      override def create(): ExecutorResource = {
        val executor = ef.create()
        val testExecutor = fromKitAndExecutor(testKit, ef.access(executor))
        (executor, testExecutor)
      }

      override def shutdown(r: ExecutorResource): Unit =
        ef.shutdown(r._1)
    }

  val defaultFactory: TestExecutor.Factory[ScalettoTestKit] =
    defaultFactory(ScalettoExecutor.defaultFactory)

  lazy val global: TestExecutor[ScalettoTestKit] =
    defaultFactory.access(defaultFactory.create())
}
