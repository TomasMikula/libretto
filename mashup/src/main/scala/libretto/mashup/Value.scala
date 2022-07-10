package libretto.mashup

import libretto.mashup.dsl.{Float64, Record, Text}
import libretto.util.Async

sealed trait Value[A] {
  def feedTo(using rt: Runtime, exn: rt.Execution)(port: exn.InPort[A]): Unit =
    ???
}

object Value {
  case class Txt(value: String) extends Value[Text]
  case class F64(value: Double) extends Value[Float64]
  case object EmptyRecord extends Value[Record]

  def text(value: String): Value[Text] =
    Txt(value)

  def float64(value: Double): Value[Float64] =
    F64(value)

  def emptyRecord: Value[Record] =
    EmptyRecord
}
