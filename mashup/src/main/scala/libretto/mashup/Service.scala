package libretto.mashup

import libretto.mashup.dsl.{Fun, Unlimited, fun}
import zio.{Scope, ZIO}
import zio.http.service.{ChannelFactory, EventLoopGroup}

object Service {
  def runSimple[A, B](
    inputs: Input[A],
    outputs: Output[B],
    blueprint: Fun[A, B],
  )(using
    runtime: Runtime,
  ): ZIO[Scope, Throwable, Unit] =
    run(inputs, outputs, Unlimited.map(blueprint))

  def runStateless[A, B](
    inputs: Input[A],
    outputs: Output[B],
    blueprint: Fun[Unlimited[A], B],
  )(using
    runtime: Runtime,
  ): ZIO[Scope, Throwable, Unit] =
    run(inputs, outputs, fun(ua => Unlimited.map(blueprint)(Unlimited.duplicate(ua))))

  def run[A, B](
    inputs: Input[A],
    outputs: Output[B],
    blueprint: Fun[Unlimited[A], Unlimited[B]],
  )(using
    runtime: Runtime,
  ): ZIO[Scope, Throwable, Unit] =
      ZIO
        .attempt(runtime.run(blueprint))
        .flatMap { executing =>
          given execution: executing.execution.type = executing.execution
          runInput(inputs, executing.inPort) zipPar runOutput(executing.outPort, outputs)
        }

  private def runInput[A](using rt: Runtime, exn: rt.Execution)(
    input: Input[A],
    inPort: exn.InPort[Unlimited[A]],
  ): ZIO[Scope, Throwable, Unit] =
    for {
      service <- ServiceInput.initialize(input)
      nothing <- service.operate(inPort)
    } yield nothing

  private def runOutput[A](using rt: Runtime, exn: rt.Execution)(
    outPort: exn.OutPort[Unlimited[A]],
    output: Output[A],
  ): ZIO[Scope, Throwable, Unit] =
    for {
      service <- ServiceOutput.initialize(output)
      nothing <- service.operate(outPort)
    } yield nothing
}
