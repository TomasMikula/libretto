package libretto.scaletto.impl.futurebased

import java.util.concurrent.{Executor as JExecutor, Executors, ExecutorService, ScheduledExecutorService}
import libretto.exec.{Executing, Executor, SupportsCustomScheduler}
import libretto.exec.Executor.CancellationReason
import libretto.lambda.Tupled
import libretto.lambda.util.SourcePos
import libretto.scaletto.impl.FreeScaletto
import libretto.util.{Async, Scheduler}
import scala.concurrent.ExecutionContext

object FutureExecutor {
  def apply(
    scheduler: ScheduledExecutorService,
    blockingExecutor: JExecutor,
  ): Executor.Ofp[FreeScaletto.type, BridgeImpl.type, ExecutionParam] = {
    val ec = ExecutionContext.fromExecutor(scheduler)
    val sc = new SchedulerFromScheduledExecutorService(scheduler)
    val blockingEC = ExecutionContext.fromExecutor(blockingExecutor)
    new FutureExecutor(ec, sc, blockingEC)
  }

  type ExecutionParam[A] = SchedulerParam[A]
  object ExecutionParam {
    def extract[A](pa: Tupled[Tuple2, ExecutionParam, A]): (Scheduler, A) = {
      type G[X] = (Scheduler, X)

      pa.foldMapWith(
        [X] => (x: SchedulerParam[X]) => (x.scheduler, x.fromUnit(())),
        { [X, Y] => (x: G[X], y: G[Y]) => (x._1, (x._2, y._2)) }
      )
    }
  }

  case class SchedulerParam[A](scheduler: Scheduler)(using ev: A =:= Unit) {
    def fromUnit(u: Unit): A = ev.flip(u)
  }

  given SupportsCustomScheduler[ExecutionParam] with {
    override def scheduler(s: libretto.util.Scheduler): ExecutionParam[Unit] =
      SchedulerParam(s)
  }

  val defaultFactory: Executor.Factory.Ofp[FreeScaletto.type, BridgeImpl.type, ExecutionParam] =
    new Executor.Factory {
      override type Dsl = FreeScaletto.type
      override type Bridge = BridgeImpl.type

      override val dsl = FreeScaletto
      override val bridge = BridgeImpl

      override type ExecutionParam[A] = FutureExecutor.ExecutionParam[A]

      override type ExecutorResource =
        (ScheduledExecutorService, ExecutorService, Executor.Ofp[dsl.type, bridge.type, ExecutionParam])

      override def name: String =
        "FutureExecutor.defaultFactory"

      override def access(r: ExecutorResource): Executor.Ofp[dsl.type, bridge.type, ExecutionParam] =
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
) extends Executor {

  override val dsl: FreeScaletto.type = FreeScaletto
  override val bridge: BridgeImpl.type = BridgeImpl

  override type ExecutionParam[A] = FutureExecutor.ExecutionParam[A]

  import dsl.-⚬
  import bridge.{Execution, cancelExecution}

  override def execute[A, B, P](
    prg: A -⚬ B,
    params: ExecutionParams[P],
  ): (Executing[bridge.type, A, B], P) = {
    val (sched, p) = params.asTupled match
      case Left(ev) => (scheduler, ev.flip(()))
      case Right(ps) => FutureExecutor.ExecutionParam.extract(ps)
    val executing = BridgeImpl.execute(prg)(ec, sched, blockingEC)
    (executing, p)
  }

  override def cancel(using pos: SourcePos)(execution: Execution): Async[Unit] =
    cancelExecution(execution, pos)

  override def watchForCancellation(execution: Execution): Async[CancellationReason] =
    bridge.watchForCancellation(execution)
}
