package libretto

import java.util.concurrent.{Executor, ScheduledExecutorService}
import libretto.impl.{FreeScalaDSL, FreeScalaFutureRunner}
import scala.concurrent.Future

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

  val coreStreams: CoreStreams[dsl.type, coreLib.type] =
    CoreStreams(dsl, coreLib)

  val scalaStreams: ScalaStreams[dsl.type, coreLib.type, scalaLib.type, coreStreams.type] =
    ScalaStreams(dsl, coreLib, scalaLib, coreStreams)

  def runner(blockingExecutor: Executor)(implicit scheduler: ScheduledExecutorService): ScalaRunner[dsl.type, Future] =
    runner0(scheduler, blockingExecutor)
}
