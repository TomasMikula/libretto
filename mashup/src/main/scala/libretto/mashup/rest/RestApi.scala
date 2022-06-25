package libretto.mashup.rest

import libretto.mashup.dsl.-->

sealed trait RestApi[A]

object RestApi {
  case class SingleEndpoint[I, O](endpoint: Endpoint[I, O]) extends RestApi[I --> O]

  def apply[I, O](endpoint: Endpoint[I, O]): RestApi[I --> O] =
    SingleEndpoint(endpoint)
}
