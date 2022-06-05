package libretto.mashup

import libretto.mashup.rest.RestApi

sealed trait Input[A]

object Input {
  case object Empty extends Input[Unit]
  case class RestApiAt[A](api: RestApi[A], uri: String) extends Input[A]

  def empty: Input[Unit] =
    Empty

  def restApiAt[A](
    api: RestApi[A],
    uri: String,
  ): Input[A] =
    RestApiAt(api, uri)
}
