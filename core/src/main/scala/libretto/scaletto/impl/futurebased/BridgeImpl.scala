package libretto.scaletto.impl.futurebased

import java.util.concurrent.{Executor => JExecutor}
import libretto.{Executing, Scheduler}
import libretto.Executor.CancellationReason
import libretto.scaletto.{ScalettoBridge, ScalettoExecution}
import libretto.scaletto.impl.FreeScaletto
import libretto.util.Async
import scala.concurrent.ExecutionContext

object BridgeImpl extends ScalettoBridge {
  override type Dsl = FreeScaletto.type
  override val dsl = FreeScaletto
  import dsl.-⚬

  override opaque type Execution <: ScalettoExecution[dsl.type] = ExecutionImpl

  def execute[A, B](prg: A -⚬ B)(
    ec: ExecutionContext,
    scheduler: Scheduler,
    blockingExecutor: JExecutor,
  ): Executing[this.type, A, B] = {
    val execution = new ExecutionImpl(new ResourceRegistry)(using ec, scheduler, blockingExecutor)
    val (in, out) = execution.execute(prg)
    Executing(using this)(execution, in, out)
  }

  def cancelExecution(exn: Execution): Async[Unit] =
    exn.cancel()

  def watchForCancellation(exn: Execution): Async[CancellationReason] =
    exn.watchForCancellation()
}
