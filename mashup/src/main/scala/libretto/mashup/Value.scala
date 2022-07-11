package libretto.mashup

import libretto.mashup.dsl.{##, Float64, Record, Text, of}
import libretto.util.Async

sealed trait Value[A] {
  def feedTo(using rt: Runtime, exn: rt.Execution)(port: exn.InPort[A]): Unit =
    ???
}

object Value {
  case class Txt(value: String) extends Value[Text]
  case class F64(value: Double) extends Value[Float64]
  case object EmptyRecord extends Value[Record]
  case class ExtendRecord[A, Name <: String, T](
    init: Value[A],
    name: Name,
    last: Value[T],
  ) extends Value[A ## (Name of T)]

  def text(value: String): Value[Text] =
    Txt(value)

  def float64(value: Double): Value[Float64] =
    F64(value)

  def emptyRecord: Value[Record] =
    EmptyRecord

  def extendRecord[A, Name <: String, T](
    init: Value[A],
    name: Name,
    last: Value[T],
  ): Value[A ## (Name of T)] =
    ExtendRecord(init, name, last)
}
