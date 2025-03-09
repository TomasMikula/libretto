package libretto.mashup

import libretto.mashup.dsl.{-->, |&|, EmptyResource, Unlimited, of}
import libretto.mashup.rest.{Endpoint, RelativeUrl, RestApi}
import scala.util.{Failure, Success}
import zio.{Scope, ZIO}
import zio.json.ast.Json
import zio.http.{Client, Request, URL, Method}

sealed trait ServiceInput[A] {
  def handleRequest(using rt: Runtime, exn: rt.Execution)(port: exn.InPort[A]): ZIO[Any, Throwable, Unit]

  def operate(using rt: Runtime, exn: rt.Execution)(port: exn.InPort[Unlimited[A]]): ZIO[Any, Throwable, Unit] =
    ZIO
      .suspend { exn.InPort.unlimitedAwaitChoice(port).toZIO }
      .flatMap {
        case Success(choice) =>
          choice match {
            case None =>
              ZIO.unit
            case Some(Left(port)) =>
              handleRequest(port)
            case Some(Right((port1, port2))) =>
              operate(port1) zipPar operate(port2)
          }
        case Failure(e) =>
          ZIO.fail(e)
      }
}

object ServiceInput {
  object Empty extends ServiceInput[EmptyResource] {
    override def handleRequest(using rt: Runtime, exn: rt.Execution)(port: exn.InPort[EmptyResource]): ZIO[Any, Throwable, Unit] =
      ZIO.succeed {
        exn.InPort.emptyResourceIgnore(port)
      }
  }

  class Rest[A](
    id: String,
    api: RestApi[A],
    baseUri: String,
    client: Client,
  ) extends ServiceInput[A] {
    override def handleRequest(using rt: Runtime, exn: rt.Execution)(port: exn.InPort[A]): ZIO[Any, Throwable, Unit] =
      api match {
        case RestApi.SingleEndpoint(endpoint) =>
          handleRequestUsingEndpoint(endpoint, port)
      }

    private def handleRequestUsingEndpoint[I, O](using rt: Runtime, exn: rt.Execution)(
      endpoint: Endpoint[I, O],
      port: exn.InPort[I --> O],
    ): ZIO[Any, Throwable, Unit] =
      ZIO
        .succeed { exn.InPort.functionInputOutput(port) }
        .flatMap {
          case (argsPort, resultPort) =>
            endpoint match {
              case Endpoint.Get(url, outputType) =>
                for {
                  urlStr <- url.fillParamsFrom(argsPort).toZIO.map(_.toEither).absolve
                  result <- getJson(s"$baseUri/$urlStr", outputType)
                } yield exn.InPort.valueSupply(resultPort, result)
            }
        }

    private def getJson[T](url: String, outputType: JsonType[T])(using rt: Runtime): ZIO[Any, Throwable, rt.Value[T]] =
      for {
        url  <- ZIO.fromEither(URL.decode(url))
        _    <- ZIO.logInfo(s"$id: Requesting $url")
        resp <- client.request(Request.get(url))
                  .tapError { e => ZIO.logError(s"Client failed with: ${e.getMessage()}").as(e) }
        body <- resp.body.asString
        _    <- ZIO.logInfo(s"$id: Response status=${resp.status}, body=$body")
        json <- parseJson(body)
        rslt <- readJson(outputType, json)
        _    <- ZIO.logInfo(s"$id: Success decoding response body")
      } yield rslt

    private def parseJson(s: String): ZIO[Any, Throwable, Json] =
      Json.decoder.decodeJson(s) match {
        case Right(json) => ZIO.succeed(json)
        case Left(msg)   => ZIO.fail(new IllegalArgumentException(s"$msg. Input: $s"))
      }

    private def readJson[A](jsonType: JsonType[A], json: Json)(using rt: Runtime): ZIO[Any, Throwable, rt.Value[A]] =
      jsonType.readJson(json) match {
        case Right(a)  => ZIO.succeed(a)
        case Left(msg) => ZIO.fail(new IllegalArgumentException(msg))
      }
  }

  class Labeled[N <: String & Singleton, T](label: N, base: ServiceInput[T]) extends ServiceInput[N of T] {
    override def handleRequest(using rt: Runtime, exn: rt.Execution)(
      port: exn.InPort[N of T],
    ): ZIO[Any, Throwable, Unit] =
      base.handleRequest(
        exn.InPort.labeledGet(port)
      )
  }

  class BinaryChoice[A, B](a: ServiceInput[A], b: ServiceInput[B]) extends ServiceInput[A |&| B] {
    override def handleRequest(using rt: Runtime, exn: rt.Execution)(
      port: exn.InPort[A |&| B],
    ): ZIO[Any, Throwable, Unit] =
      exn.InPort.choiceAwait(port).toZIO.flatMap {
        case Success(Left(pa))  => a.handleRequest(pa)
        case Success(Right(pb)) => b.handleRequest(pb)
        case Failure(e)         => ZIO.fail(e)
      }
  }

  def initialize[A](id: String, blueprint: Input[A]): ZIO[Scope, Throwable, ServiceInput[A]] =
    blueprint match {
      case Input.Empty =>
        ZIO.succeed(Empty)
      case Input.RestApiAt(api, uri) =>
        Client.default
          .build
          .map(_.get[Client])
          .map(Rest(id, api, uri, _))
      case i: Input.SingleChoice[n, t] =>
        initialize(id, i.input).map(Labeled[n, t](i.label, _))
      case i: Input.MultiChoice[x, n, y] =>
        (initialize(s"$id/l", i.base) zipWithPar initialize(s"$id/r", i.input).map(Labeled[n, y](i.label, _))) {
          (init, last) => BinaryChoice[x, n of y](init, last)
        }
    }
}
