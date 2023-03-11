package libretto

import libretto.stream.scaletto.DefaultStreams.ValSource
import libretto.util.Async
import zio.{UIO, ZIO}
import zio.stream.UStream

package object zio_interop {

  extension [A](stream: UStream[A]) {
    def asSource: Ztuff[ValSource[A]] =
      Ztuff.ZioUStream(stream)
  }

  extension [A](fa: Async[A]) {
    def toZIO: UIO[A] =
      ZIO.async(callback => fa.onComplete(a => callback(ZIO.succeed(a))))
  }

}
