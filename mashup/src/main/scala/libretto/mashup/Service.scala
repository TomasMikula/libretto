package libretto.mashup

import libretto.mashup.dsl.Fun
import zio.ZIO

object Service {
  def connectTo[A](inputs: Input[A]): ConnectingTo[A] =
    new ConnectingTo[A](inputs)

  class ConnectingTo[A](inputs: Input[A]) {
    def exposeAt[B](outputs: Output[B]): ExposingAt[A, B] =
      new ExposingAt[A, B](inputs, outputs)
  }

  class ExposingAt[A, B](inputs: Input[A], outputs: Output[B]) {
    def run(blueprint: Fun[A, B]): ZIO[Any, Nothing, Unit] =
      Service.run[A, B](inputs, outputs, blueprint)
  }

  def run[A, B](
    inputs: Input[A],
    outputs: Output[B],
    blueprint: Fun[A, B],
  ): ZIO[Any, Nothing, Unit] =
    ???
}
