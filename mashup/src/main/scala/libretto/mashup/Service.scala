package libretto.mashup

import libretto.mashup.dsl.{Fun, Unlimited}
import zio.ZIO

object Service {
  def runStateless[A, B](
    inputs: Input[A],
    outputs: Output[B],
    blueprint: Fun[A, B],
  )(using
    runtime: Runtime,
  ): ZIO[Any, Throwable, Unit] =
    run(inputs, outputs, Unlimited.map(blueprint))

  def run[A, B](
    inputs: Input[A],
    outputs: Output[B],
    blueprint: Fun[Unlimited[A], Unlimited[B]],
  )(using
    runtime: Runtime,
  ): ZIO[Any, Throwable, Unit] =
      ZIO
        .attempt(runtime.run(blueprint))
        .flatMap { case (inPort, outPort, execution) =>
          runInput(inputs, inPort) zipPar runOutput(outPort, outputs)
        }

  private def runInput[A](using rt: Runtime)(
    input: Input[A],
    inPort: rt.InPort[Unlimited[A]],
  ): ZIO[Any, Throwable, Unit] =
    ZIO.scoped {
      for {
        service <- ServiceInput.initialize(input)
        nothing <- service.handleRequestsFrom(inPort)
      } yield nothing
    }

  private def runOutput[A](using rt: Runtime)(
    outPort: rt.OutPort[Unlimited[A]],
    output: Output[A],
  ): ZIO[Any, Throwable, Unit] =
    ZIO.scoped {
      for {
        service <- ServiceOutput.initialize(output)
        nothing <- service.forwardRequestsTo(outPort)
      } yield nothing
    }
}
