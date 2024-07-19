package libretto

/** Defines interface to interact with a running Libretto program. */
trait CoreBridge {
  type Dsl <: CoreDSL

  val dsl: Dsl

  /** Handle to a running Libretto program. */
  type Execution <: CoreExecution[dsl.type]
}

object CoreBridge {
  type Of[DSL <: CoreDSL] = CoreBridge { type Dsl = DSL }
}
