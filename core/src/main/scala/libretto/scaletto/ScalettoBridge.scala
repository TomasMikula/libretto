package libretto.scaletto

import libretto.{ClosedBridge, ClosedExecution}
import libretto.util.Async

trait ScalettoBridge extends ClosedBridge {
  override type Dsl <: Scaletto

  override type Execution <: ScalettoExecution[dsl.type]
}

trait ScalettoExecution[DSL <: Scaletto] extends ClosedExecution[DSL] {
  import dsl.Val

  override val OutPort: ScalettoOutPorts
  override val InPort:  ScalettoInPorts

  trait ScalettoOutPorts extends ClosedOutPorts {
    def awaitVal[A](port: OutPort[Val[A]]): Async[Either[Throwable, A]]
  }

  trait ScalettoInPorts extends ClosedInPorts {
    def supplyVal[A](port: InPort[Val[A]], value: A): Unit
  }
}

object ScalettoBridge {
  type Of[DSL <: Scaletto] = ScalettoBridge { type Dsl = DSL }
}
