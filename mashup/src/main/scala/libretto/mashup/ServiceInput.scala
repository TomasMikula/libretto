package libretto.mashup

import libretto.mashup.dsl.{-->, EmptyResource, Unlimited}
import libretto.mashup.rest.{Endpoint, RelativeUrl, RestApi}
import zio.{Scope, ZIO}
import zio.json.ast.Json
import zhttp.http.Method
import zhttp.service.{ChannelFactory, Client, EventLoopGroup}

sealed trait ServiceInput[A] {
  def handleRequestFrom(using rt: Runtime)(port: rt.InPort[A]): ZIO[Any, Throwable, Unit]

  def handleRequestsFrom(using rt: Runtime)(port: rt.InPort[Unlimited[A]]): ZIO[Any, Throwable, Unit] =
    ZIO
      .suspend { rt.InPort.unlimitedAwaitChoice(port).toZIO }
      .flatMap {
        case None =>
          ZIO.unit
        case Some(Left(port)) =>
          handleRequestFrom(port)
        case Some(Right(port1, port2)) =>
          handleRequestsFrom(port1) zipPar handleRequestsFrom(port2)
      }
}

object ServiceInput {
  object Empty extends ServiceInput[EmptyResource] {
    override def handleRequestFrom(using rt: Runtime)(port: rt.InPort[EmptyResource]): ZIO[Any, Throwable, Unit] =
      ZIO.succeed {
        rt.InPort.emptyResourceIgnore(port)
      }
  }

  class Rest[A](
    api: RestApi[A],
    baseUri: String,
  ) extends ServiceInput[A] {
    override def handleRequestFrom(using rt: Runtime)(port: rt.InPort[A]): ZIO[Any, Throwable, Unit] =
      api match {
        case RestApi.SingleEndpoint(endpoint) =>
          handleRequestUsingEndpoint(endpoint, port)
      }

    private def handleRequestUsingEndpoint[I, O](using rt: Runtime)(
      endpoint: Endpoint[I, O],
      port: rt.InPort[I --> O],
    ): ZIO[Any, Throwable, Unit] =
      ZIO
        .suspend { rt.InPort.functionGetInOut(port).toZIO }
        .flatMap {
          case (argsPort, resultPort) =>
            endpoint match {
              case Endpoint.Get(url, outputType) =>
                for {
                  urlStr <- url.fillParamsFrom(argsPort)
                  result <- getJson(urlStr, outputType)
                  _      <- result.feedTo(resultPort)
                } yield ()
        }
      }

    extension [I](url: RelativeUrl[I]) {
      def fillParamsFrom(using rt: Runtime)(port: rt.OutPort[I]): ZIO[Any, Throwable, String] =
        ZIO.fail(new NotImplementedError)
    }

    private def getJson[T](url: String, outputType: JsonType[T]): ZIO[Any, Throwable, Value[T]] =
      ZIO.provideLayer(ChannelFactory.auto ++ EventLoopGroup.auto()) {
        for {
          resp <- Client.request(url, Method.GET)
          body <- resp.bodyAsString
          json <- parseJson(body)
          rslt <- outputType.readFromJson(json)
        } yield rslt
      }

    private def parseJson(s: String): ZIO[Any, Throwable, Json] =
      ZIO.fail(new NotImplementedError)

    extension [T](tp: JsonType[T]) {
      def readFromJson(json: Json): ZIO[Any, Throwable, Value[T]] =
        ZIO.fail(new NotImplementedError)
    }

    extension [T](value: Value[T]) {
      def feedTo(using rt: Runtime)(port: rt.InPort[T]): ZIO[Any, Throwable, Unit] =
        ZIO.fail(new NotImplementedError)
    }
  }

  def initialize[A](blueprint: Input[A]): ZIO[Any, Throwable, ServiceInput[A]] =
    blueprint match {
      case Input.Empty =>
        ZIO.succeed(Empty)
      case Input.RestApiAt(api, uri) =>
        ZIO.succeed(Rest(api, uri))
    }
}
