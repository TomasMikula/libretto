package libretto.mashup

import java.net.InetSocketAddress
import libretto.mashup.dsl.{-->, Fun, Unlimited}
import libretto.mashup.rest.{Endpoint, Path, RestApi}
import libretto.mashup.ZioHttpServer.{NextRequest, RequestStream}
import zhttp.http.{Path => ZPath, Request, Response, Status}
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

  def initialize[A](blueprint: Output[A]): ZIO[Scope, Throwable, ServiceOutput[A]] =
    blueprint match {
      case Output.RestApiAt(api, host, port) =>
        for {
          addr          <- ZIO.attemptBlocking(InetSocketAddress(host, port))
          requestStream <- ZioHttpServer.start(addr)
        } yield Rest(api, requestStream)
    }

  extension (zpath: ZPath) {
    def toPath: Path =
      zpath match {
        case ZPath(segments) =>
          if (segments.isEmpty) {
            Path.Empty
          } else {
            val segs = segments.head match {
              case ZPath.Segment.Root => segments.tail
              case _                  => segments
            }
            val revSegs = segs.reverseIterator.toList match {
              case ZPath.Segment.Text("") :: ZPath.Segment.Root :: t =>
                ZPath.Segment.Root :: t
              case ZPath.Segment.Text("") :: t =>
                ZPath.Segment.Root :: t
              case other =>
                other
            }
            revSegs match {
              case Nil =>
                Path.Empty
              case last :: revInit =>
                val (revInit1, lastSegment) =
                  last match {
                    case ZPath.Segment.Text(s) =>
                      // we know that `s` is non-empty
                      (revInit, Path.LastSegment.NonEmpty(Path.segment(s)))
                    case ZPath.Segment.Root =>
                      revInit match {
                        case Nil | ZPath.Segment.Root :: _ =>
                          (revInit, Path.LastSegment.SlashTerminated(Path.segment("")))
                        case ZPath.Segment.Text(s) :: revInit1 =>
                          (revInit1, Path.LastSegment.SlashTerminated(Path.segment(s)))
                      }
                  }

                @scala.annotation.tailrec
                def go(revInit: List[ZPath.Segment], acc: List[Path.Segment], last: Path.LastSegment): Path.NonEmpty =
                  revInit match {
                    case Nil =>
                      Path.NonEmpty(acc, last)
                    case seg :: revInit1 =>
                      seg match {
                        case ZPath.Segment.Text(s) =>
                          go(revInit1, Path.segment(s) :: acc, last)
                        case ZPath.Segment.Root =>
                          revInit1 match {
                            case Nil | ZPath.Segment.Root :: _ =>
                              go(revInit1, Path.segment("") :: acc, last)
                            case ZPath.Segment.Text(s) :: revInit2 =>
                              go(revInit2, Path.segment(s) :: acc, last)
                          }
                      }
                  }

                go(revInit1, Nil, lastSegment)
            }
          }
      }
  }
}
