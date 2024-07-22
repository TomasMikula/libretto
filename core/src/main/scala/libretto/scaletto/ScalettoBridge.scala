package libretto.scaletto

import libretto.closed.ClosedBridge
import libretto.util.Async

trait ScalettoBridge extends ClosedBridge {
  override type Dsl <: Scaletto

  override type Execution <: ScalettoExecution[dsl.type]
}

trait ScalettoExecution[DSL <: Scaletto] {
  type InPort[A]
  type OutPort[B]

  val dsl: DSL
  import dsl.Val

  val OutPort: ScalettoOutPorts
  val InPort:  ScalettoInPorts

  trait ScalettoOutPorts {
    def awaitVal[A](port: OutPort[Val[A]]): Async[Either[Throwable, A]]
  }

  trait ScalettoInPorts {
    def supplyVal[A](port: InPort[Val[A]], value: A): Unit
  }
}

object ScalettoBridge {
  type Of[DSL <: Scaletto] = ScalettoBridge { type Dsl = DSL }
}
