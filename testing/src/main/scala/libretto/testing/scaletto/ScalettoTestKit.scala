package libretto.testing.scaletto

import libretto.scaletto.{Scaletto, ScalettoBridge}
import libretto.testing.TestKit.dsl
import libretto.testing.{SupportsManualClock, TestKitOps, TestKitWithManualClock, TestResult}

trait ScalettoTestKit extends TestKitWithManualClock {
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

object ScalettoTestKit extends TestKitOps {
  type OfDsl[DSL <: Scaletto] =
    ScalettoTestKit { type Dsl = DSL }

  type Of[DSL <: Scaletto, BRDG <: ScalettoBridge.Of[DSL]] =
    OfDsl[DSL] { val bridge: BRDG }

  type Ofp[DSL <: Scaletto, BRDG <: ScalettoBridge.Of[DSL], P[_]] =
    Of[DSL, BRDG] { type ExecutionParam[A] = P[A] }

  def fromBridge[P[_]](
    dsl: Scaletto,
    bridge: ScalettoBridge.Of[dsl.type],
    manualClockSupport: SupportsManualClock[P],
  ): ScalettoTestKit.Ofp[bridge.dsl.type, bridge.type, P] =
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
