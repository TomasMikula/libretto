package libretto.mashup

import java.net.InetSocketAddress
import libretto.mashup.dsl.{-->, Fun, Unlimited}
import libretto.mashup.rest.{Endpoint, Path, RestApi}
import libretto.mashup.ZioHttpServer.{NextRequest, RequestStream}
import zio.{Promise, Ref, Scope, ZIO}
import zio.http.{Path as ZPath, Request, Response, Status}

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
    ownerServiceName: String,
    boundAt: InetSocketAddress,
    api: RestApi[A],
    requestStream: RequestStream,
  ) extends ServiceOutput[A] {

    private val id = s"$ownerServiceName REST server @ $boundAt"

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
    ): ZIO[Any, Throwable, Nothing] = {
      def loop(
        requestStream: RequestStream,
        port: exn.OutPort[Unlimited[A]],
        requestCounter: Ref[Long],
      ): ZIO[Any, Throwable, Nothing] =
        ZIO.logInfo(s"$id: waiting for next request") *>
        requestStream.next.flatMap {
          case NextRequest(req, resp, tail) =>
            requestCounter
              .updateAndGet(_ + 1)
              .flatMap { reqNo =>
                ZIO.logInfo(s"$id: Incoming request no. $reqNo: ${req.url}") *>
                (matchRequest(req) match {
                  case Some(requestMatch) =>
                    import requestMatch.{adapt, input, outputType}
                    ZIO.logInfo(s"$id: Request $reqNo understood, passing to Mashup Runtime") *>
                    ZIO.succeed {
                      val (pHead, pTail) = exn.OutPort.unlimitedUncons(port)
                      val (pi, po) = exn.OutPort.functionInputOutput(exn.OutPort.map(pHead)(adapt))
                      input.feedTo(pi)
                      (outputType.extractResponse(po), pTail)
                    }
                      .<* { ZIO.logInfo(s"$id: Awaiting result of request $reqNo from Mashup Runtime and simultaneously accepting new requests.") }
                      .flatMap { case (asyncResp, pTail) =>
                        val awaitResult =
                          asyncResp.toZIO.flatMap { res =>
                            ZIO.logInfo(s"$id: Request $reqNo: Result received from Mashup Runtime") *>
                            resp.succeed(res)
                          }
                        awaitResult &> loop(tail, pTail, requestCounter)
                      }
                  case None =>
                    ZIO.logInfo(s"$id: Request $reqNo unrecognized, returning ${Status.NotFound}") *>
                    resp.succeed(Response.status(Status.NotFound)) *>
                    loop(tail, port, requestCounter)
                })
              }
        }

      Ref.make(0L)
        .flatMap(loop(requestStream, port, _))
    }

    private def matchRequest(req: Request)(using rt: Runtime): Option[RequestMatch[rt.type, A]] =
      api match {
        case RestApi.SingleEndpoint(endpoint) =>
          endpoint.matchRequest(req)
      }

    extension [I, O](endpoint: Endpoint[I, O]) {
      private def matchRequest(res: Request)(using rt: Runtime): Option[RequestMatch[rt.type, I --> O]] =
        endpoint match {
          case Endpoint.Get(url, outputType) =>
            url
              .matchPath(res.path.toPath)
              .map(RequestMatch(dsl.id[I --> O], _, BodyType.json(outputType)))
        }
    }

    private abstract class RequestMatch[RT <: Runtime, A] {
      val runtime: RT

      type In
      type Out

      val adapt: Fun[A, In --> Out]

      val input: MappedValue[runtime.type, In]

      val outputType: BodyType[Out]
    }

    private object RequestMatch {
      def apply[A, I, O](using rt: Runtime)(
        f: Fun[A, I --> O],
        in: MappedValue[rt.type, I],
        out: BodyType[O],
      ): RequestMatch[rt.type, A] =
        new RequestMatch[rt.type, A] {
          override val runtime: rt.type = rt

          override type In  = I
          override type Out = O

          override val adapt = f
          override val input = in
          override val outputType = out
        }
    }
  }

  def initialize[A](
    ownerServiceName: String,
    blueprint: Output[A],
  ): ZIO[Scope, Throwable, ServiceOutput[A]] =
    blueprint match {
      case Output.RestApiAt(api, host, port) =>
        for {
          addr          <- ZIO.attemptBlocking(InetSocketAddress(host, port))
          requestStream <- ZioHttpServer.start(addr)
          _             <- ZIO.logInfo(s"$ownerServiceName: Started HTTP server at $addr")
        } yield Rest(ownerServiceName, addr, api, requestStream)
    }

  extension (zpath: ZPath) {
    def toPath: Path =
      zpath match {
        case ZPath(flags, segments) =>
          segments.lastOption match
            case None =>
              Path.Empty
            case Some(last) =>
              val init = segments.init.iterator.map(Path.segment(_)).toList
              val lastSeg = Path.segment(last)
              Path.NonEmpty(
                init,
                if (zpath.hasTrailingSlash)
                  Path.LastSegment.SlashTerminated(lastSeg)
                else
                  Path.LastSegment.NonEmpty(lastSeg)
              )
      }
  }
}
