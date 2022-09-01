package libretto.scaletto.impl.uberconcurrent

import libretto.scaletto.ScalettoExecution
import libretto.scaletto.impl.FreeScaletto
import libretto.util.Async
import libretto.Scheduler
import scala.concurrent.ExecutionContext

class ExecutionImpl(
  ec: ExecutionContext,
  scheduler: Scheduler,
) extends ScalettoExecution[FreeScaletto.type] {
  override val dsl = FreeScaletto

  import dsl.-⚬

  override type InPort[A] = Cell[A]
  override type OutPort[A] = Cell[A]

  override val InPort: ScalettoInPorts = ??? // TODO
  override val OutPort: ScalettoOutPorts = ??? // TODO

  def execute[A, B](prg: A -⚬ B): (InPort[A], OutPort[B]) = {
    val in = Cell.empty[A]
    val out = Cell.empty[B]
    submitJob { () => connect(in, prg, out) }
    (in, out)
  }

  private def submitJob(action: Runnable): Unit =
    ec.execute(action)

  private def connect[A, B](in: Cell[A], f: A -⚬ B, out: Cell[B]): Unit = {
    ??? // TODO
  }

  def cancel(): Async[Unit] =
    ??? // TODO
}
