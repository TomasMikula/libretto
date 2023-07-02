package libretto.mashup

import libretto.util.Async
import scala.util.{Failure, Success, Try}
import zio.Chunk
import zio.json.ast.{Json as ZioJson}
import zio.json.ast.Json.{encoder as JsonEncoder}
import zio.http.{Body, Response, Headers, Status}

sealed trait BodyType[A] {
  def extractResponse(using
    rt: Runtime,
    exn: rt.Execution,
  )(
    port: exn.OutPort[A],
  ): Async[Response]
}

object BodyType {
  case class Json[A](typ: JsonType[A]) extends BodyType[A] {
    override def extractResponse(using rt: Runtime, exn: rt.Execution)(
      port: exn.OutPort[A],
    ): Async[Response] =
      Json.extractJson(typ, port).map {
        case Success(json) =>
          val jsonStr = JsonEncoder.encodeJson(json, indent = None)
          Response(Status.Ok, Headers.empty, Body.fromCharSequence(jsonStr))
        case Failure(e) =>
          Response(Status.InternalServerError, Headers.empty, Body.fromString(e.getMessage))
      }
  }

  object Json {
    import JsonType.*

    private def extractJson[A](using rt: Runtime, exn: rt.Execution)(
      typ: JsonType[A],
      port: exn.OutPort[A],
    ): Async[Try[ZioJson]] =
      typ match {
        case JsonTypeText =>
          exn.OutPort.textGet(port).map(_.map(ZioJson.Str(_)))
        case JsonTypeFloat64 =>
          exn.OutPort.float64Get(port).map(_.map(ZioJson.Num(_)))
        case JsonTypeObject(typ) =>
          extractJsonObject(typ, port)
      }

    private def extractJsonObject[A](using rt: Runtime, exn: rt.Execution)(
      typ: ObjectType[A],
      port: exn.OutPort[A],
    ): Async[Try[ZioJson.Obj]] =
      typ match {
        case ObjectType.EmptyRecord =>
          val () = exn.OutPort.recordIgnoreEmpty(port)
          Async.now(Success(ZioJson.Obj()))
        case r: ObjectType.SingleFieldRecord[n, t] =>
          val pt = exn.OutPort.recordGetSingle[n, t](port)
          extractJson(r.typ, pt).map(_.map(json => ZioJson.Obj(r.name -> json)))
        case r: ObjectType.NonEmptyRecord[x, n, y] =>
          val (portInit, portLast) = exn.OutPort.recordUnsnoc[x, n, y](port)
          for {
            initFields <- extractJsonObject(r.init, portInit)
            lastField  <- extractJson(r.typ, portLast)
          } yield  {
            for {
              initFields <- initFields
              lastField  <- lastField
            } yield ZioJson.Obj(initFields.fields ++ Chunk.single((r.name, lastField)))
          }
      }
  }

  def json[A](jsonType: JsonType[A]): BodyType[A] =
    Json(jsonType)
}
