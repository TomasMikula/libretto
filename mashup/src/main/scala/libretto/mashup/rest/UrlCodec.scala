package libretto.mashup.rest

import libretto.mashup.dsl.Fun
import libretto.mashup.dsl.Fun.or

final case class UrlCodec[A](
  encode: Fun[A, String],
  decode: Fun[String, String or A],
)

object UrlCodec {
  given UrlCodec[String] =
    UrlCodec(
      Fun.id[String],
      Fun.left[String, String],
    )
}
