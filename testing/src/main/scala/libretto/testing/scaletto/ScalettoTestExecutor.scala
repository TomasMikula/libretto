package libretto.testing.scaletto

import libretto.exec.ExecutionParams
import libretto.lambda.util.Exists
import libretto.scaletto.{Scaletto, ScalettoBridge, ScalettoExecutor}
import libretto.testing.{ManualClock, TestExecutor, TestResult}
import scala.concurrent.duration.FiniteDuration

object ScalettoTestExecutor {

  class ScalettoTestKitFromBridge[DSL <: Scaletto, Bridge <: ScalettoBridge.Of[DSL]](
    val dsl0: DSL,
    val bridge0: Bridge & ScalettoBridge.Of[dsl0.type],
  ) extends ScalettoTestKit {
      override type Dsl = bridge.dsl.type

      override val dsl: bridge0.dsl.type = bridge0.dsl
      override val bridge: bridge0.type = bridge0

      override type ExecutionParam[A] = ScalettoTestExecutor.ExecutionParam[A]

      override def manualClockParam: ExecutionParam[ManualClock] =
        ExecutionParam.ManualClockParam
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

  def fromKitAndExecutor(
    kit: ScalettoTestKit,
    exr: ScalettoExecutor.Of[kit.dsl.type, kit.bridge.type],
    adaptParams: [A] => kit.ExecutionParams[A] => Exists[[X] =>> (exr.ExecutionParams[X], X => A)],
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
        adaptParams(params) match
          case e @ Exists.Some((params, adapter)) =>
            TestExecutor
              .usingExecutor(exr)
              .runTestCase[O, e.T, Y](
                body,
                params,
                (port, x) => Outcome.toAsyncTestResult(conduct(port, adapter(x))),
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
        val exr = ef.access(executor)
        val adaptParams: [A] => testKit.ExecutionParams[A] => Exists[[X] =>> (exr.ExecutionParams[X], X => A)] =
          [A] => ScalettoTestExecutor.ExecutionParam.adapt(_)(exr.schedulerParam)
        val testExecutor = fromKitAndExecutor(testKit, exr, adaptParams)
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
