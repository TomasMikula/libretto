package libretto.mashup.rest

import libretto.util.Async
import libretto.mashup.Runtime
import libretto.mashup.dsl
import libretto.mashup.dsl.{Float64, Fun, Text, ValueType, or}
import scala.util.Try

/** Supports encoding and decoding values to and from String. */
trait StringCodec[A] {
  def valueType: ValueType[A]

  def encode(using rt: Runtime)(value: rt.Value[A]): String
  def decode(using rt: Runtime)(s: String): Either[String, rt.Value[A]]

  def encodeFrom(using rt: Runtime, exn: rt.Execution)(port: exn.OutPort[A]): Async[Try[String]] =
    exn.OutPort.valueGet(port)(using valueType)
      .map(_.map(encode(_)))
}

object StringCodec {
  def apply[A: ValueType](
    encoder: (rt: Runtime) ?=> rt.Value[A] => String,
    decoder: (rt: Runtime) ?=> String => Either[String, rt.Value[A]],
  ) =
    new StringCodec[A] {
      override def valueType: ValueType[A] =
        summon[ValueType[A]]

      override def encode(using rt: Runtime)(value: rt.Value[A]): String =
        encoder(value)

      override def decode(using rt: Runtime)(s: String): Either[String, rt.Value[A]] =
        decoder(s)
    }

  given StringCodec[Text] =
    new StringCodec[Text] {
      override def valueType: ValueType[Text] =
        summon[ValueType[Text]]
      override def encode(using rt: Runtime)(value: rt.Value[Text]): String =
        rt.Value.textGet(value)

      override def decode(using rt: Runtime)(s: String): Either[String, rt.Value[Text]] =
        Right(rt.Value.text(s))
    }

  given StringCodec[Float64] =
    new StringCodec[Float64] {
      override def valueType: ValueType[Float64] =
        summon[ValueType[Float64]]

      override def encode(using rt: Runtime)(value: rt.Value[Float64]): String =
        java.lang.Double.toString(rt.Value.float64Get(value))

      override def decode(using rt: Runtime)(s: String): Either[String, rt.Value[Float64]] =
        try {
          Right(rt.Value.float64(java.lang.Double.parseDouble(s)))
        } catch {
          case e: NumberFormatException => Left(e.getMessage)
        }
    }
}
