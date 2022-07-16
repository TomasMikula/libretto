package libretto.mashup

import libretto.mashup.dsl.Fun

sealed trait MappedValue[RT <: Runtime, I] {
  val runtime: RT

  def feedTo(using exn: runtime.Execution)(port: exn.InPort[I]): Unit
}

object MappedValue {
  class Pure[RT <: Runtime, I](
    val runtime: RT,
    val value: runtime.Value[I],
  ) extends MappedValue[RT, I] {

    override def feedTo(using exn: runtime.Execution)(port: exn.InPort[I]): Unit =
      exn.InPort.valueSupply(port, value)
  }

  class Mapped[RT <: Runtime, I, J](
    val runtime: RT,
    val value: runtime.Value[I],
    val f: Fun[I, J],
  ) extends MappedValue[RT, J] {

    override def feedTo(using exn: runtime.Execution)(port: exn.InPort[J]): Unit = {
      val pi = exn.InPort.contramap(port)(f)
      exn.InPort.valueSupply(pi, value)
    }
  }

  def pure[I](using rt: Runtime)(value: rt.Value[I]): MappedValue[rt.type, I] =
    Pure(rt, value)

  def mapped[I, J](using rt: Runtime)(value: rt.Value[I], f: Fun[I, J]): MappedValue[rt.type, J] =
    Mapped(rt, value, f)
}