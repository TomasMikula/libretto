package libretto.scaletto.impl.uberconcurrent

import libretto.{Executing, ExecutionParams}
import libretto.scaletto.ScalettoExecutor
import libretto.scaletto.impl.FreeScaletto
import libretto.util.Async
import libretto.Scheduler

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
        case _: One[SchedulerParam] =>
          (None, ())
        case z: Zip[SchedulerParam, a, b] =>
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
}

class ExecutorImpl(
  scheduler: Scheduler,
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
    val executing = BridgeImpl.execute(prg)(sched)
    (executing, p)
  }

  override def cancel(execution: bridge.Execution): Async[Unit] =
    bridge.cancelExecution(execution)
}
