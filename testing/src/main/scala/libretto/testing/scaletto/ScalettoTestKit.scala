package libretto.testing.scaletto

import libretto.scaletto.{Scaletto, ScalettoBridge}
import libretto.testing.TestKit.dsl
import libretto.testing.{TestKitOps, TestKitWithManualClock, TestResult}

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
  type Of[DSL <: Scaletto] = ScalettoTestKit { type Dsl = DSL }
}
