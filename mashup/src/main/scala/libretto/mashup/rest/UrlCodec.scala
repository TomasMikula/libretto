package libretto.mashup.rest

import libretto.mashup.dsl
import libretto.mashup.dsl.{Fun, Text, or}

final case class UrlCodec[A](
  encode: Fun[A, Text],
  decode: Fun[Text, Text or A],
)

object UrlCodec {
  given UrlCodec[Text] =
    UrlCodec(
      dsl.id[Text],
      dsl.left[Text, Text],
    )
}
