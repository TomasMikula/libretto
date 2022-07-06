package libretto.mashup.rest

import libretto.mashup.JsonType
import libretto.mashup.dsl.Expr

sealed trait Endpoint[I, O]

object Endpoint {
  case class Get[I, O](url: RelativeUrl[I], outputType: JsonType[O]) extends Endpoint[I, O]

  def get[I, O: JsonType](f: RelativeUrl[I]): Endpoint[I, O] =
    Get(f, summon[JsonType[O]])
}
