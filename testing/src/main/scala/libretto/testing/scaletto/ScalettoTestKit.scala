package libretto.testing.scaletto

import libretto.CoreLib
import libretto.scaletto.{Scaletto, ScalettoBridge}
import libretto.testing.TestKit.dsl
import libretto.testing.{TestKitOps, TestKitWithManualClock, TestResult}

trait ScalettoTestKit extends TestKitWithManualClock {
  override type Dsl <: Scaletto

  override val bridge: ScalettoBridge.Of[dsl.type]

  import dsl.*
  import bridge.Execution

  private lazy val coreLib = CoreLib(dsl)
  import coreLib.*

  def leftOrCrash[A, B](msg: String = "Expected Left, was Right"): (A |+| B) -⚬ A =
    |+|.signalR > either(id[A], crashWhenDone[B, A](msg))

  def rightOrCrash[A, B](msg: String = "Expected Right, was Left"): (A |+| B) -⚬ B =
    |+|.signalL > either(crashWhenDone[A, B](msg), id[B])

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

object ScalettoTestKit extends ScalettoTestKitOps {
  type Of[DSL <: Scaletto] = ScalettoTestKit { type Dsl = DSL }
}

trait ScalettoTestKitOps extends TestKitOps {

  def leftOrCrash[A, B](using kit: ScalettoTestKit)(msg: String = "Expected Left, was Right"): dsl.-⚬[dsl.|+|[A, B], A] =
    kit.leftOrCrash(msg)

  def rightOrCrash[A, B](using kit: ScalettoTestKit)(msg: String = "Expected Right, was Left"): dsl.-⚬[dsl.|+|[A, B], B] =
    kit.rightOrCrash(msg)
}
