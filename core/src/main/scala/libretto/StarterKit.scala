package libretto

import java.util.concurrent.{Executor => JExecutor, Executors, ScheduledExecutorService}
import libretto.impl.{FreeScalaDSL, FreeScalaFutureRunner}
import scala.concurrent.{ExecutionContext, Future}
import scala.util.{Failure, Success}

object StarterKit extends StarterKit

class StarterKit extends AbstractStarterKit(FreeScalaDSL, (scheduler, blockingExecutor) => new FreeScalaFutureRunner(scheduler, blockingExecutor))

abstract class AbstractStarterKit(
  val dsl: ScalaDSL,
  val executor0: (ScheduledExecutorService, JExecutor) => ScalaExecutor.OfDsl[dsl.type],
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

  def executor(blockingExecutor: JExecutor)(implicit scheduler: ScheduledExecutorService): ScalaExecutor.OfDsl[dsl.type] =
    executor0(scheduler, blockingExecutor)

  def runner(blockingExecutor: JExecutor)(implicit scheduler: ScheduledExecutorService): ScalaRunner[dsl.type] = {
    val ec = ExecutionContext.fromExecutor(scheduler)

    ScalaRunner.fromExecutor(
      dsl,
      executor(blockingExecutor),
    )
  }

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
