package libretto.closed

import libretto.CoreBridge

trait ClosedBridge extends CoreBridge {
  override type Dsl <: ClosedDSL

  override type Execution <: ClosedExecution[dsl.type]
}

object ClosedBridge {
  type Of[DSL <: ClosedDSL] = ClosedBridge { type Dsl = DSL }
}
