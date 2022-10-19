package libretto.scaletto.impl.concurrentcells

import libretto.scaletto.{ScalettoBridge, ScalettoExecution}
import libretto.scaletto.impl.FreeScaletto
import libretto.util.{Async, SourcePos}
import libretto.{Executing, Scheduler}
import libretto.Executor.CancellationReason
import scala.concurrent.ExecutionContext

object BridgeImpl extends ScalettoBridge {
  override type Dsl = FreeScaletto.type
  override val dsl = FreeScaletto

  override opaque type Execution <: ScalettoExecution[dsl.type] = ExecutionImpl

  import dsl.-⚬

  def execute[A, B](prg: A -⚬ B)(
    ec: ExecutionContext,
    scheduler: Scheduler,
  ): Executing[this.type, A, B] = {
    val execution = new ExecutionImpl(ec, scheduler)
    val (in, out) = execution.execute(prg)
    Executing(using this)(execution, in, out)
  }

  def cancelExecution(exn: Execution, origin: SourcePos): Async[Unit] =
    exn.cancel(CancellationReason.User(origin))

  def watchForCancellation(exn: Execution): Async[CancellationReason] =
    exn.watchForCancellation()
}