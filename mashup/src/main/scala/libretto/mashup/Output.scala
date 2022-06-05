package libretto.mashup

import libretto.mashup.rest.RestApi

sealed trait Output[A]

object Output {
  case class RestApiAt[A](api: RestApi[A], host: String, port: Int) extends Output[A]

  def restApiAt[A](
    api: RestApi[A],
    host: String,
    port: Int,
  ): Output[A] =
    RestApiAt(api, host, port)
}
