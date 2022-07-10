package libretto.mashup

import java.net.InetSocketAddress
import libretto.mashup.dsl.{-->, Fun, Unlimited}
import libretto.mashup.rest.{Endpoint, RestApi}
import libretto.mashup.ZioHttpServer.{NextRequest, RequestStream}
import zhttp.http.{Request, Response, Status}
import zio.{Promise, Scope, ZIO}

sealed trait ServiceOutput[A] {
  def operate(using
    rt: Runtime,
    exn: rt.Execution
  )(
    port: exn.OutPort[Unlimited[A]],
  ): ZIO[Any, Throwable, Nothing]
}

object ServiceOutput {
  class Rest[A](
    api: RestApi[A],
    requestStream: RequestStream,
  ) extends ServiceOutput[A] {

    override def operate(using
      rt: Runtime,
      exn: rt.Execution,
    )(
      port: exn.OutPort[Unlimited[A]],
    ): ZIO[Any, Throwable, Nothing] =
      operate(requestStream, port)

    private def operate(using
      rt: Runtime,
      exn: rt.Execution,
    )(
      requestStream: RequestStream,
      port: exn.OutPort[Unlimited[A]],
    ): ZIO[Any, Throwable, Nothing] =
      requestStream.next.flatMap {
        case NextRequest(req, resp, tail) =>
          matchRequest(req) match {
            case Some(requestMatch) =>
              import requestMatch.{adapt, input, outputType}
              val (pHead, pTail) = exn.OutPort.unlimitedUncons(port)
              val (pi, po) = exn.OutPort.functionInputOutput(exn.OutPort.map(pHead)(adapt))
              input.feedTo(pi)
              outputType.extractResponse(po).toZIO.flatMap(resp.succeed) &> operate(tail, pTail)
            case None =>
              resp.succeed(Response.status(Status.NotFound)) *>
              operate(tail, port)
          }
      }

    private def matchRequest(req: Request): Option[RequestMatch[A]] =
      api match {
        case RestApi.SingleEndpoint(endpoint) =>
          endpoint.matchRequest(req)
      }

    extension [I, O](endpoint: Endpoint[I, O]) {
      private def matchRequest(res: Request): Option[RequestMatch[I --> O]] =
        endpoint match {
          case Endpoint.Get(url, outputType) =>
            url
              .matchPath(res.path)
              .map(RequestMatch(dsl.id[I --> O], _, BodyType.json(outputType)))
        }
    }

    private abstract class RequestMatch[A] {
      type In
      type Out

      val adapt: Fun[A, In --> Out]

      val input: Value[In]

      val outputType: BodyType[Out]
    }

    private object RequestMatch {
      def apply[A, I, O](
        f: Fun[A, I --> O],
        in: Value[I],
        out: BodyType[O],
      ): RequestMatch[A] =
        new RequestMatch[A] {
          override type In  = I
          override type Out = O

          override val adapt = f
          override val input = in
          override val outputType = out
        }
    }
  }

  def initialize[A](blueprint: Output[A]): ZIO[Scope, Throwable, ServiceOutput[A]] =
    blueprint match {
      case Output.RestApiAt(api, host, port) =>
        for {
          addr          <- ZIO.attemptBlocking(InetSocketAddress(host, port))
          requestStream <- ZioHttpServer.start(addr)
        } yield Rest(api, requestStream)
    }
}
