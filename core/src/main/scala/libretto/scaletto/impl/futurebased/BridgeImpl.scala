package libretto.scaletto.impl.futurebased

import libretto.exec.Executing
import libretto.exec.Executor.CancellationReason
import libretto.lambda.util.SourcePos
import libretto.scaletto.{ScalettoBridge, ScalettoExecution}
import libretto.scaletto.impl.FreeScaletto
import libretto.util.{Async, Scheduler}
import scala.concurrent.ExecutionContext

object BridgeImpl extends ScalettoBridge {
  override type Dsl = FreeScaletto.type
  override val dsl: FreeScaletto.type = FreeScaletto
  import dsl.-⚬

  override opaque type Execution <: ScalettoExecution[dsl.type] = ExecutionImpl

  def execute[A, B](prg: A -⚬ B)(
    ec: ExecutionContext,
    scheduler: Scheduler,
    blockingEC: ExecutionContext,
  ): Executing[this.type, A, B] = {
    val execution = new ExecutionImpl(new ResourceRegistry, blockingEC)(using ec, scheduler)
    val (in, out) = execution.execute(prg)
    Executing(using this)(execution, in, out)
  }

  def cancelExecution(exn: Execution, pos: SourcePos): Async[Unit] =
    exn.cancel(pos)

  def watchForCancellation(exn: Execution): Async[CancellationReason] =
    exn.watchForCancellation()

  extension [I](using exn: Execution)(port: exn.InPort[I]) {
    override def prepend[H](f: H -⚬ I): exn.InPort[H] =
      exn.InPort.contramap(port)(f)
  }

  extension [O](using exn: Execution)(port: exn.OutPort[O]) {
    override def append[P](f: O -⚬ P): exn.OutPort[P] =
      exn.OutPort.map(port)(f)
  }
}
