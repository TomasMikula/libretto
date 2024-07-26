package libretto.testing.scaletto

import libretto.exec.{ExecutionParams, Executor, SupportsCustomScheduler}
import libretto.lambda.util.Exists
import libretto.scaletto.{Scaletto, ScalettoBridge, ScalettoExecutor}
import libretto.testing.{ManualClock, SupportsManualClock, TestExecutor}
import scala.concurrent.duration.FiniteDuration

object ScalettoTestExecutor {

  sealed trait ExecutionParam[A]

  object ExecutionParam extends SupportsManualClock[ExecutionParam] {
    case object ManualClockParam extends ExecutionParam[ManualClock]

    override def manualClock: ExecutionParam[ManualClock] =
      ManualClockParam

    def adaptParam[P[_]](
      schedulerParam: libretto.util.Scheduler => P[Unit],
    ): [A] => ExecutionParam[A] => Exists[[X] =>> (P[X], X => A)] =
      [A] => (a: ExecutionParam[A]) =>
        a match {
          case ManualClockParam =>
            val (clock, scheduler) = ManualClock.scheduler()
            Exists((schedulerParam(scheduler), _ => clock))
        }
  }

  def defaultFactory(
    ef: Executor.Factory.Of[Scaletto, ScalettoBridge],
  )(using
    ep: SupportsCustomScheduler[ef.ExecutionParam],
  ): TestExecutor.Factory[ScalettoTestKit.OfDsl[ef.dsl.type]] =
    new TestExecutor.Factory[ScalettoTestKit.OfDsl[ef.dsl.type]] {
      override val testKit: ScalettoTestKit.Ofp[ef.dsl.type, ef.bridge.type, ExecutionParam] =
        ScalettoTestKit.fromBridge[ExecutionParam](ef.dsl, ef.bridge, ExecutionParam)

      override def name: String =
        s"ScalettoTestExecutor.defaultFactory(${ef.name})"

      override type ExecutorResource = (ef.ExecutorResource, TestExecutor[testKit.type])

      override def access(r: ExecutorResource): TestExecutor[testKit.type] =
        r._2

      override def create(): ExecutorResource = {
        val executor = ef.create()
        val exr = ef.access(executor)
        val testExecutor = TestExecutor
          .forKit(testKit)
          .adaptParams[exr.ExecutionParam](ExecutionParam.adaptParam(ep.scheduler))
          .usingExecutor(exr)
          .make(name)
        (executor, testExecutor)
      }

      override def shutdown(r: ExecutorResource): Unit =
        ef.shutdown(r._1)
    }

  val defaultFactory: TestExecutor.Factory[ScalettoTestKit] =
    ScalettoExecutor.withDefaultFactory {
      (fac: Executor.Factory.Of[Scaletto, ScalettoBridge]) =>
        (ev: SupportsCustomScheduler[fac.ExecutionParam]) =>
          defaultFactory(fac)(using ev)
    }

  lazy val global: TestExecutor[ScalettoTestKit] =
    defaultFactory.access(defaultFactory.create())
}
