package libretto.testing.scaletto

import libretto.exec.ExecutionParams
import libretto.lambda.util.Exists
import libretto.scaletto.{Scaletto, ScalettoBridge, ScalettoExecutor}
import libretto.testing.{ManualClock, TestExecutor}
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
        val testExecutor = TestExecutor
          .forKit(testKit)
          .adaptParams(ScalettoTestExecutor.ExecutionParam.adaptParam(exr.schedulerParam))
          .usingExecutor(exr)
          .make(name)
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
