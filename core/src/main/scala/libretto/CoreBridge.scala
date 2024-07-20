package libretto

import libretto.exec.Bridge

trait CoreBridge extends Bridge {
  override type Dsl <: CoreDSL
  override type Execution <: CoreExecution[dsl.type]
}

object CoreBridge {
  type Of[DSL <: CoreDSL] = CoreBridge { type Dsl = DSL }
}
