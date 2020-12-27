package libretto

import java.util.concurrent.ScheduledExecutorService
import libretto.impl.{FreeScalaDSL, FreeScalaFutureRunner}
import scala.concurrent.Future

object StarterKit extends StarterKit(FreeScalaDSL, scheduler => new FreeScalaFutureRunner(scheduler))

abstract class StarterKit(
  val dsl: ScalaDSL,
  val runner0: ScheduledExecutorService => ScalaRunner[dsl.type, Future],
) {
  val coreLib: CoreLib[dsl.type] =
    CoreLib(dsl)
    
  val scalaLib: ScalaLib[dsl.type, coreLib.type] =
    ScalaLib(dsl, coreLib)
    
  def runner(implicit scheduler: ScheduledExecutorService): ScalaRunner[dsl.type, Future] =
    runner0(scheduler)
}
