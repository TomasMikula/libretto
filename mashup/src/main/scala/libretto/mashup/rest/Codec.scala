package libretto.mashup.rest

import libretto.mashup.Runtime
import libretto.mashup.dsl
import libretto.mashup.dsl.{Fun, Text, or}

trait Codec[A] {
  def encode(using rt: Runtime)(value: rt.Value[A]): String
  def decode(using rt: Runtime)(s: String): Either[String, rt.Value[A]]
}

object Codec {
  def apply[A](
    encoder: (rt: Runtime) ?=> rt.Value[A] => String,
    decoder: (rt: Runtime) ?=> String => Either[String, rt.Value[A]],
  ) =
    new Codec[A] {
      override def encode(using rt: Runtime)(value: rt.Value[A]): String =
        encoder(value)

      override def decode(using rt: Runtime)(s: String): Either[String, rt.Value[A]] =
        decoder(s)
    }

  given Codec[Text] =
    new Codec[Text] {
      def encode(using rt: Runtime)(value: rt.Value[Text]): String =
        rt.Value.textGet(value)

      def decode(using rt: Runtime)(s: String): Either[String, rt.Value[Text]] =
        Right(rt.Value.text(s))
    }
}
