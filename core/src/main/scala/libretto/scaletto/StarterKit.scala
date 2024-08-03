package libretto.scaletto

import java.util.concurrent.{Executor as JExecutor, Executors, ScheduledExecutorService}
import libretto.crash.CrashLib
import libretto.exec.{Executor, SupportsCustomScheduler}
import libretto.puro.PuroLib
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
  val executorFactory: Executor.Factory.Of[dsl.type, bridge.type],
  val executor0: (ScheduledExecutorService, JExecutor) => Executor.Of[dsl.type, bridge.type],
)(using
  val supportsCustomScheduler: SupportsCustomScheduler[executorFactory.ExecutionParam],
) {
  val puroLib: PuroLib[dsl.type] =
    PuroLib(dsl)

  val scalettoLib: ScalettoLib[dsl.type, puroLib.type] =
    ScalettoLib(dsl, puroLib)

  val crashLib: CrashLib[dsl.type] =
    CrashLib(dsl)

  def executor(blockingExecutor: JExecutor)(
    scheduler: ScheduledExecutorService,
  ): Executor.Of[dsl.type, bridge.type] =
    executor0(scheduler, blockingExecutor)

  export dsl.*
  export puroLib.{dsl => _, *}
  export scalettoLib.{dsl => _, puroLib => _, *, given}

  def runScalaAsync[A](blueprint: Done -⚬ Val[A]): Future[A] = {
    val mainExecutor = Executors.newScheduledThreadPool(Runtime.getRuntime.availableProcessors())
    val blockingExecutor = Executors.newCachedThreadPool()
    given ExecutionContextExecutor = ExecutionContext.fromExecutor(mainExecutor)
    val exec = executor(blockingExecutor)(mainExecutor)

    val executing = exec.execute(blueprint)
    import executing.{execution, inPort, outPort}
    given execution.type = execution

    inPort.supplyDone()
    Async
      .toFuture { outPort.awaitVal() }
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
