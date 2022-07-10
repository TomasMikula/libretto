package libretto.mashup

import java.net.InetSocketAddress
import zhttp.http._
import zhttp.service.Server
import zio.{Fiber, Promise, Queue, Scope, UIO, ZIO}

object ZioHttpServer {
  case class RequestStream(next: UIO[NextRequest])

  case class NextRequest(
    request: Request,
    response: Promise[Nothing, Response],
    tail: RequestStream,
  )

  private def makeApp: UIO[(UHttpApp, RequestStream)] =
    for {
      queue  <- Queue.bounded[Promise[Nothing, NextRequest]](1)
      output <- Promise.make[Nothing, NextRequest]
      _      <- queue.offer(output)
    } yield {
      val app =
        Http.fromFunctionZIO { (req: Request) =>
          for {
            resp <- Promise.make[Nothing, Response]
            next <- Promise.make[Nothing, NextRequest]
            out  <- queue.take
            _    <- queue.offer(next)
            _    <- out.succeed(NextRequest(req, resp, RequestStream(next.await)))
            resp <- resp.await
          } yield resp
        }
      (app, RequestStream(output.await))
    }

  def start(address: InetSocketAddress): ZIO[Scope, Throwable, RequestStream] =
    makeApp.flatMap { case (app, requestStream) =>
      Server
        .start(address, app)
        .forkScoped
        .flatMap { fiber =>
          fiber.await.flatMap { exit =>
            ZIO.console.flatMap { _.printLine(s"Server exited with $exit") }
          }.fork
        }
        .as(requestStream)
    }
}
