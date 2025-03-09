package libretto.mashup

import libretto.mashup.dsl.{Fun, Unlimited, fun}
import zio.{Scope, ZIO}

object Service {
  def runSimple[A, B](
    serviceName: String,
    inputs: Input[A],
    outputs: Output[B],
    blueprint: Fun[A, B],
  )(using
    runtime: Runtime,
  ): ZIO[Scope, Throwable, Unit] =
    run(serviceName, inputs, outputs, Unlimited.map(blueprint))

  def runStateless[A, B](
    serviceName: String,
    inputs: Input[A],
    outputs: Output[B],
    blueprint: Fun[Unlimited[A], B],
  )(using
    runtime: Runtime,
  ): ZIO[Scope, Throwable, Unit] =
    run(serviceName, inputs, outputs, fun(ua => Unlimited.map(blueprint)(Unlimited.duplicate(ua))))

  def run[A, B](
    serviceName: String,
    inputs: Input[A],
    outputs: Output[B],
    blueprint: Fun[Unlimited[A], Unlimited[B]],
  )(using
    runtime: Runtime,
  ): ZIO[Scope, Throwable, Unit] =
      ZIO
        .attempt(runtime.run(blueprint))
        .<* { ZIO.logInfo(s"Instantiated blueprint of service $serviceName, going to bind to I/O") }
        .flatMap { executing =>
          given execution: executing.execution.type = executing.execution
          runInput(serviceName, inputs, executing.inPort) zipPar runOutput(serviceName, executing.outPort, outputs)
        }

  private def runInput[A](using rt: Runtime, exn: rt.Execution)(
    serviceName: String,
    input: Input[A],
    inPort: exn.InPort[Unlimited[A]],
  ): ZIO[Scope, Throwable, Unit] =
    for {
      service <- ServiceInput.initialize(s"$serviceName/input", input)
      _       <- ZIO.logInfo(s"Service $serviceName bound to input.")
      nothing <- service.operate(inPort)
    } yield nothing

  private def runOutput[A](using rt: Runtime, exn: rt.Execution)(
    serviceName: String,
    outPort: exn.OutPort[Unlimited[A]],
    output: Output[A],
  ): ZIO[Scope, Throwable, Unit] =
    for {
      service <- ServiceOutput.initialize(s"$serviceName/output", output)
      _       <- ZIO.logInfo(s"Service $serviceName bound to output.")
      nothing <- service.operate(outPort)
    } yield nothing
}
