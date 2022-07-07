package libretto.mashup

import libretto.mashup.dsl.Unlimited
import zio.{Scope, ZIO}

sealed trait ServiceOutput[A] {
  def forwardRequestsTo(using rt: Runtime)(port: rt.OutPort[Unlimited[A]]): ZIO[Any, Throwable, Nothing] =
    ZIO.fail(new NotImplementedError)
}

object ServiceOutput {
  def initialize[A](blueprint: Output[A]): ZIO[Scope, Throwable, ServiceOutput[A]] =
    ZIO.fail(new NotImplementedError)
}
