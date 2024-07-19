package libretto

trait ClosedBridge extends CoreBridge {
  override type Dsl <: ClosedDSL

  override type Execution <: ClosedExecution[dsl.type]
}

object ClosedBridge {
  type Of[DSL <: ClosedDSL] = ClosedBridge { type Dsl = DSL }
}
