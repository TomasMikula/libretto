package libretto.testing.scaletto

import libretto.exec.{Executor, SupportsCustomScheduler}
import libretto.lambda.util.Exists
import libretto.scaletto.{Scaletto, ScalettoBridge, ScalettoExecutor}
import libretto.testing.{ManualClock, SupportsManualClock, TestExecutor, TestKit}
import scala.concurrent.duration.FiniteDuration

object ScalettoTestExecutor {

  sealed trait ExecutionParam[A]

  object ExecutionParam {
    case object ManualClockParam extends ExecutionParam[ManualClock]

    given SupportsManualClock[ExecutionParam] with
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
  ): TestExecutor.Factory[ScalettoTestKit & TestKit.OfDsl[ef.dsl.type]] =
    TestExecutor.Factory.from[Scaletto, ScalettoBridge, ScalettoTestKit, ExecutionParam](
      ef,
      ScalettoTestKit.factory[ExecutionParam],
      ExecutionParam.adaptParam(ep.scheduler),
    )

  val defaultFactory: TestExecutor.Factory[ScalettoTestKit] =
    ScalettoExecutor.withDefaultFactory {
      (fac: Executor.Factory.Of[Scaletto, ScalettoBridge]) =>
        (ev: SupportsCustomScheduler[fac.ExecutionParam]) =>
          defaultFactory(fac)(using ev)
    }

  lazy val global: TestExecutor[ScalettoTestKit] =
    defaultFactory.access(defaultFactory.create())
}
