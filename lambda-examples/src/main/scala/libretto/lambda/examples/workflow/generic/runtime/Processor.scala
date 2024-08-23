package libretto.lambda.examples.workflow.generic.runtime

import libretto.lambda.{UnhandledCase, Unzippable}
import libretto.lambda.examples.workflow.generic.lang.**
import libretto.lambda.examples.workflow.generic.runtime.{WorkflowInProgress as WIP}
import libretto.lambda.util.SourcePos

import java.util.concurrent.{ArrayBlockingQueue, BlockingQueue, ScheduledExecutorService, TimeUnit}
import scala.concurrent.{Future, Promise}
import scala.concurrent.duration.FiniteDuration
import scala.util.{Failure, Success}

private[runtime] class Processor[Action[_, _], Val[_]](
  persistor: Persistor[Action, Val],
  worker: ActionExecutor[Action, Val],
  schedule: (FiniteDuration, () => Unit) => Unit, // TODO: must use durable timers
  workQueue: BlockingQueue[WorkItem],
  stopSignal: Promise[Unit],
)(using
  Value.Compliant[Val],
) {
  def notify(item: WorkItem): Unit =
    workQueue.put(item)

  private def loop(): Unit = {
    def poll(): Option[WorkItem] =
      Option(workQueue.poll())
        .orElse(persistor.pollWorkItem())
        .orElse(Option(workQueue.poll(5, TimeUnit.SECONDS)))
        .orElse { println(s"Nothing to do"); None }

    while (!stopSignal.future.isCompleted) {
      poll()
        .foreach { processItem(_) }
    }
  }

  private def processItem(item: WorkItem): Unit =
    item match {
      case WorkItem.Wakeup(ref) =>
        persistor.modifyOpt(ref) { crankOpt(ref, _) }
      case WorkItem.ReadingComplete(wf, pid) =>
        persistor.fetchReadValue(pid) match
          case Some(result) =>
            supplyValue(wf, pid, result)
          case None =>
            Console.err.println(s"Non-existent promise $pid")
      case WorkItem.ActionComplete(wf, id) =>
        persistor.fetchActionResult(id) match
          case Some(result) =>
            result match
              case Success(value) =>
                supplyValue(wf, id, value)
              case Failure(e) =>
                failWorkflow(wf, e)
          case None =>
            Console.err.println(s"Non-existent action run $id")
      case WorkItem.TimerElapsed(wRef, timerId) =>
        UnhandledCase.raise(s"$item")
    }

  private def supplyValue[R, A](
    ref: WorkflowRef[R],
    id: PortId[A] | ActionRunId[A],
    result: Value[Val, A],
  ): Unit =
    persistor.modifyOpt(ref) {
      case WorkflowInProgress.IncompleteImpl(input, cont, resultAcc) =>
        input
          .supplyValue(id, result)
          .map { input =>
            WorkflowInProgress.IncompleteImpl(input, cont, resultAcc)
          }
      case WorkflowInProgress.Completed(result) =>
        Console.err.println(s"Supplying promise result to an already completed workflow.")
        None
      case WorkflowInProgress.Failed(_, _) =>
        // do nothing
        None
    }

  private def failWorkflow[A](
    w: WorkflowRef[A],
    e: Throwable,
  ): Unit =
    persistor.modifyOpt(w) {
      case WorkflowInProgress.Failed(_, _) =>
        None
      case WorkflowInProgress.Completed(_) =>
        Console.err.println(s"Completed workflow received a failed promise.")
        None
      case w: WorkflowInProgress.Incomplete[act, val_, a] =>
        Some(WorkflowInProgress.Failed(e, w))
    }

  private def crankOpt[A](ref: WorkflowRef[A], w: WIP[Action, Val, A]): Option[WIP[Action, Val, A]] =
    crank(ref, w) match
      case CrankRes.AlreadyIrreducible(_) => None
      case CrankRes.Progressed(w1)        => Some(w1)

  private def crank[A](ref: WorkflowRef[A], w: WIP[Action, Val, A]): CrankRes[A] =
    w match
      case w @ WIP.Completed(_) =>
        CrankRes.AlreadyIrreducible(w)
      case w @ WIP.Failed(_, _) =>
        CrankRes.AlreadyIrreducible(w)
      case w: WIP.Incomplete[op, v, a] =>
        w.crank match
          case WIP.CrankRes.AlreadyStuck(w) =>
            CrankRes.AlreadyIrreducible(w)
          case WIP.CrankRes.Progressed(w) =>
            CrankRes.Progressed(w)
          case ask: WIP.CrankRes.Ask[action, val_, x, a] =>
            val px = persistor.newInputPort[x](ref)
            val w1 = ask.cont(Input.portName(ref, px), Input.reading(px))
            CrankRes.Progressed(w1)
          case WIP.CrankRes.SetTimer(timeout, cont) =>
            val timerId = new TimerId

            // TODO: elapsed timer must go through persistor first
            schedule(timeout, () => notify(WorkItem.TimerElapsed(ref, timerId)))

            val w1 = cont(timerId)
            CrankRes.Progressed(w1)
          case req: WIP.CrankRes.ActionRequest[action, val_, x, y, a] =>
            val actionRunId = persistor.recordRunningAction[x, y](ref, req.input, req.action)
            worker.submit(req.input, req.action) { result =>
              persistor.completeAction(actionRunId, result)
              workQueue.put(WorkItem.ActionComplete(ref, actionRunId))
            }
            val w1 = req.cont(Input.awaitingAction(actionRunId))
            CrankRes.Progressed(w1)

  private enum CrankRes[A]:
    case AlreadyIrreducible(w: WIP[Action, Val, A])
    case Progressed(w: WIP[Action, Val, A])
}

private[runtime] object Processor {

  def start[Action[_, _], Val[_]](
    persistor: Persistor[Action, Val],
    worker: ActionExecutor[Action, Val],
    scheduler: ScheduledExecutorService,
  )(using
    Value.Compliant[Val],
  ): Processor[Action, Val] = {
    val queue = new ArrayBlockingQueue[WorkItem](1000)
    val stopSignal = Promise[Unit]
    val schedule = (timeout: FiniteDuration, action: () => Unit) =>
      scheduler.schedule((() => action()): Runnable, timeout.toMillis, TimeUnit.MILLISECONDS): Unit
    val processor = new Processor(persistor, worker, schedule, queue, stopSignal)
    val processorThread = new Thread {
      override def run(): Unit = processor.loop()
    }
    processorThread.setName("WorkflowProcessor")
    processorThread.setDaemon(true)
    processorThread.setUncaughtExceptionHandler((t, e) => e.printStackTrace(Console.err))
    processorThread.start()
    processor
  }

}
