package libretto.mashup

import libretto.util.Async
import zhttp.http.Response

sealed trait BodyType[A] {
  def extractResponse(using
    rt: Runtime,
    exn: rt.Execution,
  )(
    port: exn.OutPort[A],
  ): Async[Response] =
    ???
}

object BodyType {
  case class Json[A](value: JsonType[A]) extends BodyType[A]

  def json[A](jsonType: JsonType[A]): BodyType[A] =
    Json(jsonType)
}
