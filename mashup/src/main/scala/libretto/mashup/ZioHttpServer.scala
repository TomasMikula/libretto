package libretto.mashup

import java.net.InetSocketAddress
import zio.http.*
import zio.{
  Promise,
  Queue,
  Scope,
  UIO,
  ZIO,
  ZLayer
}

object ZioHttpServer {
  case class RequestStream(next: UIO[NextRequest])

  case class NextRequest(
    request: Request,
    response: Promise[Nothing, Response],
    tail: RequestStream,
  )

  private def makeApp(addr: String): UIO[(Route[Scope, Response], RequestStream)] =
    for {
      queue  <- Queue.bounded[Promise[Nothing, NextRequest]](1)
      output <- Promise.make[Nothing, NextRequest]
      _      <- queue.offer(output)
    } yield {
      val app =
        Route.route(RoutePattern.any)(Handler.fromFunctionZIO[(Path, Request)] { case (_, req) =>
          for {
            _    <- ZIO.logInfo(s"Received request at $addr: ${req.url}")
            resp <- Promise.make[Nothing, Response]
            next <- Promise.make[Nothing, NextRequest]
            out  <- queue.take
            _    <- queue.offer(next)
            _    <- out.succeed(NextRequest(req, resp, RequestStream(next.await)))
            resp <- resp.await
          } yield resp
        })
      (app, RequestStream(output.await))
    }

  def start(address: InetSocketAddress): ZIO[Scope, Throwable, RequestStream] =
    makeApp(address.toString).flatMap { case (app, requestStream) =>
      Server
        .serve(app)
        .provideSome[Scope](
          ZLayer.succeed(Server.Config.default.binding(address)),
          Server.live,
        )
        .forkScoped
        .flatMap { fiber =>
          fiber.await.flatMap { exit =>
            ZIO.console.flatMap { _.printLine(s"Server exited with $exit") }
          }.fork
        }
        .as(requestStream)
    }
}
