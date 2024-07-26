package libretto.closed

import libretto.core.CoreBridge

trait ClosedBridge extends CoreBridge {
  override type Dsl <: ClosedDSL

  import dsl.=⚬

  extension [I, O](using exn: Execution)(port: exn.InPort[I =⚬ O]) {
    def simulateFunction(): (exn.OutPort[I], exn.InPort[O])
  }

  extension [I, O](using exn: Execution)(port: exn.OutPort[I =⚬ O]) {
    def useFunction(): (exn.InPort[I], exn.OutPort[O])
  }
}

object ClosedBridge {
  type Of[DSL <: ClosedDSL] = ClosedBridge { type Dsl = DSL }
}
