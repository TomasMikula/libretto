package libretto.exec

/** Defines interface to interact with a running Libretto program. */
trait Bridge {
  type Dsl <: { type -⚬[A, B] }

  val dsl: Dsl

  /** Handle to a running Libretto program. */
  type Execution <: libretto.exec.Execution

  import dsl.-⚬

  extension [I](using exn: Execution)(port: exn.InPort[I]) {
    def prepend[H](f: H -⚬ I): exn.InPort[H]
  }

  extension [O](using exn: Execution)(port: exn.OutPort[O]) {
    infix def append[P](f: O -⚬ P): exn.OutPort[P]
  }
}

object Bridge {
  type Of[DSL <: { type -⚬[A, B] }] = Bridge { type Dsl = DSL }
}
