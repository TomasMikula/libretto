package libretto.scaletto

import java.util.concurrent.{Executor as JExecutor, Executors, ScheduledExecutorService}
import libretto.{CoreLib, ClosedLib, InvertLib}
import libretto.scaletto.impl.FreeScaletto
import libretto.scaletto.impl.futurebased.{BridgeImpl, FutureExecutor}
import libretto.util.Async
import scala.concurrent.{ExecutionContext, Future}
import scala.util.{Failure, Success}
import scala.concurrent.ExecutionContextExecutor

object StarterKit extends StarterKit

class StarterKit extends AbstractStarterKit(
  FreeScaletto,
  BridgeImpl,
  FutureExecutor.defaultFactory,
  (scheduler, blockingExecutor) => FutureExecutor(scheduler, blockingExecutor),
)

abstract class AbstractStarterKit(
  val dsl: Scaletto,
  val bridge: ScalettoBridge.Of[dsl.type],
  val executorFactory: ScalettoExecutor.Factory.Of[dsl.type, bridge.type],
  val executor0: (ScheduledExecutorService, JExecutor) => ScalettoExecutor.Of[dsl.type, bridge.type],
) {
  val coreLib: CoreLib[dsl.type] =
    CoreLib(dsl)

  val scalettoLib: ScalettoLib[dsl.type, coreLib.type] =
    ScalettoLib(dsl, coreLib)

  val closedLib: ClosedLib[dsl.type, coreLib.type] =
    ClosedLib(dsl, coreLib)

  val invertLib: InvertLib[coreLib.type] =
    InvertLib(coreLib)

  def executor(blockingExecutor: JExecutor)(
    scheduler: ScheduledExecutorService,
  ): ScalettoExecutor.Of[dsl.type, bridge.type] =
    executor0(scheduler, blockingExecutor)

  export dsl.*
  export coreLib.{dsl => _, *}
  export scalettoLib.{dsl => _, coreLib => _, *, given}
  export closedLib.{dsl => _, coreLib => _, *}
  export invertLib.{coreLib => _, *}

  def runScalaAsync[A](blueprint: Done -⚬ Val[A]): Future[A] = {
    val mainExecutor = Executors.newScheduledThreadPool(Runtime.getRuntime.availableProcessors())
    val blockingExecutor = Executors.newCachedThreadPool()
    given ExecutionContextExecutor = ExecutionContext.fromExecutor(mainExecutor)
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
