package libretto.mashup

import libretto.mashup.dsl.Unlimited
import zio.{Scope, ZIO}

sealed trait InputService[A] {
  def handleRequestsFrom(using rt: Runtime)(port: rt.InPort[Unlimited[A]]): ZIO[Any, Throwable, Nothing]
}

object InputService {
  def initialize[A](blueprint: Input[A]): ZIO[Scope, Throwable, InputService[A]] =
    ZIO.fail(new NotImplementedError)
}
