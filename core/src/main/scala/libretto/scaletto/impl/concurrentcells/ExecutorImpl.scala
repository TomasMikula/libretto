package libretto.scaletto.impl.concurrentcells

import java.util.concurrent.{Executor => JExecutor, ExecutorService, Executors, ScheduledExecutorService}
import libretto.{Executing, ExecutionParams}
import libretto.Executor.CancellationReason
import libretto.scaletto.ScalettoExecutor
import libretto.scaletto.impl.FreeScaletto
import libretto.util.{Async, SourcePos}
import libretto.Scheduler
import scala.concurrent.ExecutionContext

object ExecutorImpl {
  type ExecutionParam[A] = ExecutionParams.Free[SchedulerParam, A]
  object ExecutionParam extends ExecutionParams.WithScheduler[ExecutionParam] {
    override def pair[A, B](a: ExecutionParam[A], b: ExecutionParam[B]): ExecutionParam[(A, B)] =
      ExecutionParams.Free.pair(a, b)

    override def unit: ExecutionParam[Unit] =
      ExecutionParams.Free.unit

    override def scheduler(s: Scheduler): ExecutionParam[Unit] =
      ExecutionParams.Free.wrap(SchedulerParam(s))

    def extract[A](pa: ExecutionParam[A]): (Option[Scheduler], A) = {
      import ExecutionParams.Free.{One, Zip, Ext}
      pa match {
        case Ext(sp @ SchedulerParam(scheduler)) =>
          (Some(scheduler), sp.fromUnit(()))
        case _: One[sp] =>
          (None, ())
        case z: Zip[sp, a, b] =>
          (extract[a](z.a), extract[b](z.b)) match {
            case ((None, a), (s, b)) => (s, (a, b))
            case ((s, a), (None, b)) => (s, (a, b))
            case ((Some(s1), a), (Some(s2), b)) => throw new IllegalArgumentException("Scheduler specified twice")
          }
      }
    }
  }

  case class SchedulerParam[A](scheduler: Scheduler)(using ev: A =:= Unit) {
    def fromUnit(u: Unit): A = ev.flip(u)
  }

  def factory: ScalettoExecutor.Factory =
    new ScalettoExecutor.Factory {
      override type Dsl = FreeScaletto.type
      override type Bridge = BridgeImpl.type

      val dsl: Dsl = FreeScaletto
      val bridge: Bridge = BridgeImpl

      override type ExecutorResource =
        (ScheduledExecutorService, ExecutorService, ScalettoExecutor.Of[dsl.type, bridge.type])

      override def name =
        "concurrentcells"

      override def access(r: ExecutorResource): ScalettoExecutor.Of[dsl.type, bridge.type] =
        r._3

      override def create(): ExecutorResource = {
        val scheduledExecutor = Executors.newScheduledThreadPool(Runtime.getRuntime().availableProcessors())
        val scheduler: Scheduler = (d, f) => scheduledExecutor.schedule((() => f()): Runnable, d.length, d.unit)
        val ec = ExecutionContext.fromExecutor(scheduledExecutor)
        val blockingExecutor = Executors.newCachedThreadPool()
        val executor = new ExecutorImpl(ec, scheduler, blockingExecutor)
        (scheduledExecutor, blockingExecutor, executor)
      }

      override def shutdown(r: ExecutorResource): Unit = {
        r._2.shutdownNow()
        r._1.shutdownNow()
      }
    }
}

class ExecutorImpl(
  ec: ExecutionContext,
  scheduler: Scheduler,
  blockingExecutor: JExecutor,
) extends ScalettoExecutor {
  override type Dsl = FreeScaletto.type
  override val dsl: Dsl = FreeScaletto

  override type Bridge = BridgeImpl.type
  override val bridge: Bridge = BridgeImpl

  override type ExecutionParam[A] =
    ExecutorImpl.ExecutionParam[A]
  override val ExecutionParam: ExecutionParams.WithScheduler[ExecutionParam] =
    ExecutorImpl.ExecutionParam

  import dsl.-⚬

  override def execute[A, B, P](
    prg: A -⚬ B,
    params: ExecutionParam[P],
  ): (Executing[bridge.type, A, B], P) = {
    val (schedOpt, p) = ExecutorImpl.ExecutionParam.extract(params)
    val sched = schedOpt.getOrElse(scheduler)
    val executing = BridgeImpl.execute(prg)(ec, sched)
    (executing, p)
  }

  override def cancel(using pos: SourcePos)(execution: bridge.Execution): Async[Unit] =
    bridge.cancelExecution(execution, pos)

  override def watchForCancellation(execution: bridge.Execution): Async[CancellationReason] =
    bridge.watchForCancellation(execution)
}
