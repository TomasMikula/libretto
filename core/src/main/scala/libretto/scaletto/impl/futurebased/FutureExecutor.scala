package libretto.scaletto.impl.futurebased

import java.util.concurrent.{Executor as JExecutor, Executors, ExecutorService, ScheduledExecutorService}
import libretto.{Executing, ExecutionParams, Scheduler}
import libretto.Executor.CancellationReason
import libretto.lambda.util.SourcePos
import libretto.scaletto.ScalettoExecutor
import libretto.scaletto.impl.FreeScaletto
import libretto.util.Async
import scala.concurrent.ExecutionContext
import scala.annotation.nowarn

object FutureExecutor {
  def apply(
    scheduler: ScheduledExecutorService,
    blockingExecutor: JExecutor,
  ): ScalettoExecutor.Of[FreeScaletto.type, BridgeImpl.type] = {
    val ec = ExecutionContext.fromExecutor(scheduler)
    val sc = new SchedulerFromScheduledExecutorService(scheduler)
    val blockingEC = ExecutionContext.fromExecutor(blockingExecutor)
    new FutureExecutor(ec, sc, blockingEC)
  }

  type ExecutionParam[A] = ExecutionParams.Free[SchedulerParam, A]
  object ExecutionParam extends ExecutionParams.WithScheduler[ExecutionParam] {
    override def unit: ExecutionParam[Unit] =
      ExecutionParams.Free.unit
    override def pair[A, B](a: ExecutionParam[A], b: ExecutionParam[B]): ExecutionParam[(A, B)] =
      ExecutionParams.Free.pair(a, b)
    override def scheduler(s: Scheduler): ExecutionParam[Unit] =
      ExecutionParams.Free.wrap(SchedulerParam(s))

    @nowarn("msg=type test")
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

  val defaultFactory: ScalettoExecutor.Factory.Of[FreeScaletto.type, BridgeImpl.type] =
    new ScalettoExecutor.Factory {
      override type Dsl = FreeScaletto.type
      override type Bridge = BridgeImpl.type

      override val dsl = FreeScaletto
      override val bridge = BridgeImpl

      override type ExecutorResource =
        (ScheduledExecutorService, ExecutorService, ScalettoExecutor.Of[dsl.type, bridge.type])

      override def name: String =
        "FutureExecutor.defaultFactory"

      override def access(r: ExecutorResource): ScalettoExecutor.Of[dsl.type, bridge.type] =
        r._3

      override def create(): ExecutorResource = {
        val scheduler = Executors.newScheduledThreadPool(Runtime.getRuntime().availableProcessors())
        val blockingExecutor = Executors.newCachedThreadPool()
        val executor = FutureExecutor(scheduler, blockingExecutor)
        (scheduler, blockingExecutor, executor)
      }

      override def shutdown(r: ExecutorResource): Unit = {
        r._2.shutdownNow()
        r._1.shutdownNow()
      }
    }
}

/** Executor of [[FreeScaletto]] based on [[Future]]s and [[Promise]]s.
  *
  * It is known to be flawed by design in that it might create long (potentially infinite) chains of [[Promise]]s.
  * This could be solved with a custom implementation of promises/futures that support unregistration of listeners.
  *
  * On top of that, expect bugs, since the implementation is full of unsafe type casts, because Scala's (including
  * Dotty's) type inference cannot cope with the kind of pattern matches found here.
  */
class FutureExecutor(
  ec: ExecutionContext,
  scheduler: Scheduler,
  blockingEC: ExecutionContext,
) extends ScalettoExecutor {

  override type Dsl = FreeScaletto.type
  override type Bridge = BridgeImpl.type

  override val dsl = FreeScaletto
  override val bridge = BridgeImpl

  override type ExecutionParam[A] = FutureExecutor.ExecutionParam[A]
  override val ExecutionParam: ExecutionParams.WithScheduler[ExecutionParam] =
    FutureExecutor.ExecutionParam

  import dsl.-⚬
  import bridge.{Execution, cancelExecution}

  override def execute[A, B, P](
    prg: A -⚬ B,
    params: ExecutionParam[P],
  ): (Executing[bridge.type, A, B], P) = {
    val (schedOpt, p) = FutureExecutor.ExecutionParam.extract(params)
    val sched = schedOpt.getOrElse(scheduler)
    val executing = BridgeImpl.execute(prg)(ec, sched, blockingEC)
    (executing, p)
  }

  override def cancel(using pos: SourcePos)(execution: Execution): Async[Unit] =
    cancelExecution(execution, pos)

  override def watchForCancellation(execution: Execution): Async[CancellationReason] =
    bridge.watchForCancellation(execution)
}
