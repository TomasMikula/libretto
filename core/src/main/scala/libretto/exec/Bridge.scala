package libretto.exec

/** Defines interface to interact with a running Libretto program. */
trait Bridge {
  type Dsl <: { type -⚬[A, B] }

  val dsl: Dsl

  /** Handle to a running Libretto program. */
  type Execution <: libretto.exec.Execution[dsl.type]
}

object Bridge {
  type Of[DSL <: { type -⚬[A, B] }] = Bridge { type Dsl = DSL }
}
