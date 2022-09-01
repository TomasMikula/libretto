package libretto.scaletto.impl.uberconcurrent

import libretto.scaletto.{ScalettoBridge, ScalettoExecution}
import libretto.scaletto.impl.FreeScaletto
import libretto.util.Async
import libretto.{Executing, Scheduler}

object BridgeImpl extends ScalettoBridge {
  override type Dsl = FreeScaletto.type
  override val dsl = FreeScaletto

  override opaque type Execution <: ScalettoExecution[dsl.type] = ExecutionImpl

  import dsl.-⚬

  def execute[A, B](prg: A -⚬ B)(
    scheduler: Scheduler,
  ): Executing[this.type, A, B] = {
    val execution = new ExecutionImpl(using scheduler)
    val (in, out) = execution.execute(prg)
    Executing(using this)(execution, in, out)
  }

  def cancelExecution(exn: Execution): Async[Unit] =
    exn.cancel()
}
