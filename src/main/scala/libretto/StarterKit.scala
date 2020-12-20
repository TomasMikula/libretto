package libretto

import libretto.impl.{FreeScalaDSL, FreeScalaFutureRunner}
import scala.concurrent.{ExecutionContext, Future}

object StarterKit extends StarterKit(FreeScalaDSL, ec => new FreeScalaFutureRunner()(ec))

abstract class StarterKit(
  val dsl: ScalaDSL,
  val runner0: ExecutionContext => ScalaRunner[dsl.type, Future],
) {
  val coreLib: CoreLib[dsl.type] =
    CoreLib(dsl)
    
  val scalaLib: ScalaLib[dsl.type, coreLib.type] =
    ScalaLib(dsl, coreLib)
    
  def runner(implicit ec: ExecutionContext): ScalaRunner[dsl.type, Future] =
    runner0(ec)
}
