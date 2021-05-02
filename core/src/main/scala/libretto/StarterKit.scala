package libretto

import java.util.concurrent.{Executor, Executors, ScheduledExecutorService}
import libretto.impl.{FreeScalaDSL, FreeScalaFutureRunner}
import scala.concurrent.{ExecutionContext, Future}
import scala.util.{Failure, Success}

object StarterKit extends StarterKit

class StarterKit extends AbstractStarterKit(FreeScalaDSL, (scheduler, blockingExecutor) => new FreeScalaFutureRunner(scheduler, blockingExecutor))

abstract class AbstractStarterKit(
  val dsl: ScalaDSL,
  val runner0: (ScheduledExecutorService, Executor) => ScalaRunner[dsl.type, Future],
) {
  val coreLib: CoreLib[dsl.type] =
    CoreLib(dsl)

  val scalaLib: ScalaLib[dsl.type, coreLib.type] =
    ScalaLib(dsl, coreLib)

  val crashLib: CrashLib[dsl.type, coreLib.type] =
    CrashLib(dsl, coreLib)

  val closedLib: ClosedLib[dsl.type, coreLib.type] =
    ClosedLib(dsl, coreLib)

  val invertLib: InvertLib[coreLib.type] =
    InvertLib(coreLib)

  val coreStreams: CoreStreams[dsl.type, coreLib.type] =
    CoreStreams(dsl, coreLib)

  val scalaStreams: ScalaStreams[dsl.type, coreLib.type, scalaLib.type, coreStreams.type] =
    ScalaStreams(dsl, coreLib, scalaLib, coreStreams)

  def runner(blockingExecutor: Executor)(implicit scheduler: ScheduledExecutorService): ScalaRunner[dsl.type, Future] =
    runner0(scheduler, blockingExecutor)

  import dsl._
  import coreLib._

  def runScalaAsync[A](blueprint: Done -⚬ Val[A]): Future[A] = {
    val mainExecutor = Executors.newScheduledThreadPool(Runtime.getRuntime.availableProcessors())
    val blockingExecutor = Executors.newCachedThreadPool()
    implicit val ec = ExecutionContext.fromExecutor(mainExecutor)

    runner(blockingExecutor)(mainExecutor)
      .runScala(blueprint)
      .map { res =>
        blockingExecutor.shutdown()
        mainExecutor.shutdown()
        res
      }
  }

  def runAsync(blueprint: Done -⚬ Done): Future[Unit] =
    runScalaAsync(blueprint > constVal(()))
}
