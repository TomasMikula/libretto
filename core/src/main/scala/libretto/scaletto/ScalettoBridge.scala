package libretto.scaletto

import libretto.ClosedBridge
import libretto.util.Async

trait ScalettoBridge extends ClosedBridge {
  override type Dsl <: Scaletto

  import dsl.Val

  override type Execution <: ScalettoExecution

  trait ScalettoExecution extends ClosedExecution {
    override val OutPort: ScalettoOutPorts
    override val InPort:  ScalettoInPorts

    trait ScalettoOutPorts extends ClosedOutPorts {
      def awaitVal[A](port: OutPort[Val[A]]): Async[Either[Throwable, A]]
    }

    trait ScalettoInPorts extends ClosedInPorts {
      def supplyVal[A](port: InPort[Val[A]], value: A): Unit
    }
  }
}

object ScalettoBridge {
  type Of[DSL <: Scaletto] = ScalettoBridge { type Dsl = DSL }
}
