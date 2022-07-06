package libretto.mashup

import libretto.mashup.dsl.Unlimited
import zio.{Scope, ZIO}

sealed trait OutputService[A] {
  def forwardRequestsTo(using rt: Runtime)(port: rt.OutPort[Unlimited[A]]): ZIO[Any, Throwable, Nothing] =
    ZIO.fail(new NotImplementedError)
}

object OutputService {
  def initialize[A](blueprint: Output[A]): ZIO[Scope, Throwable, OutputService[A]] =
    ZIO.fail(new NotImplementedError)
}
