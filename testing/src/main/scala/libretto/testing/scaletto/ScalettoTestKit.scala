package libretto.testing.scaletto

import libretto.exec.Bridge
import libretto.scaletto.{Scaletto, ScalettoBridge}
import libretto.testing.TestKit
import libretto.testing.{SupportsManualClock, TestKitWithManualClock, TestResult}
import libretto.testing.core.CoreTestKit

trait ScalettoTestKit extends CoreTestKit with TestKitWithManualClock {
  override type Dsl <: Scaletto

  override val bridge: ScalettoBridge.Of[dsl.type]

  import dsl.Val
  import bridge.Execution

  extension [A](using exn: Execution)(port: exn.OutPort[Val[A]]) {
    def expectVal: Outcome[A] =
      Outcome.asyncTestResult(
        port.awaitVal().map {
          case Left(e)  => TestResult.crash(e)
          case Right(a) => TestResult.success(a)
        }
      )
  }
}

object ScalettoTestKit {

  def factory[P[_]](using SupportsManualClock[P]): TestKit.Factory[Scaletto, ScalettoBridge, ScalettoTestKit, P] =
    new TestKit.Factory[Scaletto, ScalettoBridge, ScalettoTestKit, P] {
      override def name =
        "ScalettoTestKit.factory"

      override def create(
        dsl: Scaletto,
        bridge: ScalettoBridge & Bridge.Of[dsl.type],
      ): ScalettoTestKit & TestKit.Ofp[dsl.type, bridge.type, P] =
        fromBridge[P](dsl, bridge, summon)
    }

  private def fromBridge[P[_]](
    dsl: Scaletto,
    bridge: ScalettoBridge.Of[dsl.type],
    manualClockSupport: SupportsManualClock[P],
  ): ScalettoTestKit & TestKit.Ofp[bridge.dsl.type, bridge.type, P] =
    new ScalettoTestKitFromBridge(dsl, bridge, manualClockSupport)

  private class ScalettoTestKitFromBridge[DSL <: Scaletto, Bridge <: ScalettoBridge.Of[DSL], P[_]](
    val dsl0: DSL,
    val bridge0: Bridge & ScalettoBridge.Of[dsl0.type],
    override val manualClockSupport: SupportsManualClock[P],
  ) extends ScalettoTestKit {
      override type Dsl = bridge.dsl.type

      override val dsl: bridge0.dsl.type = bridge0.dsl
      override val bridge: bridge0.type = bridge0

      override type ExecutionParam[A] = P[A]
  }
}
