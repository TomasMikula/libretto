package libretto

import java.util.concurrent.{Executor => JExecutor, Executors, ScheduledExecutorService}
import libretto.impl.{FreeScalaDSL, FreeScalaFutureRunner}
import libretto.util.Async
import scala.concurrent.{ExecutionContext, Future}
import scala.util.{Failure, Success}
import libretto.impl.FreeScalaFutureBridge

object StarterKit extends StarterKit

class StarterKit extends AbstractStarterKit(
  FreeScalaDSL,
  FreeScalaFutureBridge,
  (scheduler, blockingExecutor) => FreeScalaFutureRunner(scheduler, blockingExecutor),
)

abstract class AbstractStarterKit(
  val dsl: ScalaDSL,
  val bridge: ScalaBridge.Of[dsl.type],
  val executor0: (ScheduledExecutorService, JExecutor) => ScalaExecutor.Of[dsl.type, bridge.type],
) {
  val coreLib: CoreLib[dsl.type] =
    CoreLib(dsl)

  val scalaLib: ScalaLib[dsl.type, coreLib.type] =
    ScalaLib(dsl, coreLib)

  val closedLib: ClosedLib[dsl.type, coreLib.type] =
    ClosedLib(dsl, coreLib)

  val invertLib: InvertLib[coreLib.type] =
    InvertLib(coreLib)

  val coreStreams: CoreStreams[dsl.type, coreLib.type] =
    CoreStreams(dsl, coreLib)

  val scalaStreams: ScalaStreams[dsl.type, coreLib.type, scalaLib.type, coreStreams.type] =
    ScalaStreams(dsl, coreLib, scalaLib, coreStreams)

  def executor(blockingExecutor: JExecutor)(implicit
    scheduler: ScheduledExecutorService,
  ): ScalaExecutor.Of[dsl.type, bridge.type] =
    executor0(scheduler, blockingExecutor)

  export dsl._
  export coreLib.{dsl => _, _}
  export scalaLib.{dsl => _, coreLib => _, _}
  export closedLib.{dsl => _, coreLib => _, _}
  export invertLib.{coreLib => _, _}
  export coreStreams.{dsl => _, _}
  export scalaStreams.{dsl => _, coreLib => _, scalaLib => _, coreStreams => _, _}

  def runScalaAsync[A](blueprint: Done -⚬ Val[A]): Future[A] = {
    val mainExecutor = Executors.newScheduledThreadPool(Runtime.getRuntime.availableProcessors())
    val blockingExecutor = Executors.newCachedThreadPool()
    implicit val ec = ExecutionContext.fromExecutor(mainExecutor)
    val exec = executor(blockingExecutor)(mainExecutor)

    val executing = exec.execute(blueprint)
    import executing.{execution, inPort, outPort}

    execution.InPort.supplyDone(inPort)
    Async
      .toFuture { execution.OutPort.awaitVal(outPort) }
      .flatMap {
        case Right(a) => Future.successful(a)
        case Left(e)  => Future.failed(e)
      }
      .andThen { _ =>
        exec.cancel(execution) // should not be necessary, but the Future-based impl sometimes does not release all resources before completion
        blockingExecutor.shutdown()
        mainExecutor.shutdown()
      }
  }

  def runAsync(blueprint: Done -⚬ Done): Future[Unit] =
    runScalaAsync(blueprint > constVal(()))
}
