package libretto.scaletto

import libretto.puro.PuroBridge
import libretto.util.Async

trait ScalettoBridge extends PuroBridge {
  override type Dsl <: Scaletto

  import dsl.Val

  extension [A](using exn: Execution)(port: exn.InPort[Val[A]]) {
    def supplyVal(value: A): Unit
  }

  extension [A](using exn: Execution)(port: exn.OutPort[Val[A]]) {
    def awaitVal(): Async[Either[Throwable, A]]
  }
}

object ScalettoBridge {
  type Of[DSL <: Scaletto] = ScalettoBridge { type Dsl = DSL }
}
