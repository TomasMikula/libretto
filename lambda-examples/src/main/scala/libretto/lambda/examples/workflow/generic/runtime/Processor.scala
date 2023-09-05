package libretto.lambda.examples.workflow.generic.runtime

import libretto.lambda.Unzippable
import libretto.lambda.examples.workflow.generic.lang.**
import libretto.lambda.util.SourcePos

import java.util.concurrent.{ArrayBlockingQueue, BlockingQueue, TimeUnit}
import scala.concurrent.{Future, Promise}

private[runtime] class Processor[Action[_, _], Val[_]](
  persistor: Persistor[Action, Val],
  workQueue: BlockingQueue[WorkItem],
  stopSignal: Promise[Unit],
)(using
  Unzippable[**, Val],
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
        .foreach { processItem(persistor, _) }
    }
  }

  private def processItem(
    persistor: Persistor[Action, Val],
    item: WorkItem,
  ): Unit =
    println(s"processItem($item)")
    item match {
      case WorkItem.Wakeup(ref) =>
        persistor.modifyOpt(ref) { crankOpt(_) }
    }

  private def crankOpt[A](w: WIP[Action, Val, A]): Option[WIP[Action, Val, A]] =
    crank(w) match
      case CrankRes.AlreadyIrreducible(_) => None
      case CrankRes.Progressed(w1)  => Some(w1)

  private def crank[A](w: WIP[Action, Val, A]): CrankRes[A] =
    w.crank match
      case WIP.CrankRes.AlreadyIrreducible(w) =>
        CrankRes.AlreadyIrreducible(w)
      case WIP.CrankRes.Progressed(w) =>
        CrankRes.Progressed(w)
      case ask: WIP.CrankRes.Ask[action, val_, x, a] =>
        val promiseId = persistor.promise[x]
        val w1 = ask.cont(promiseId)
        CrankRes.Progressed(w1)
      case WIP.CrankRes.ActionRequest(input, action, cont) =>
        throw NotImplementedError(s"at ${summon[SourcePos]}")

    // w match {
    //   case w: WIP.Irreducible[Action, Val, A] =>
    //     // nothing to do, false alarm
    //     CrankRes.AlreadyIrreducible(w)

    //   case WIP.Zip(a1, a2) =>
    //     println(w)
    //     ???

    //   case WIP.Map(a, f) =>
    //     crank(a) match
    //       case CrankRes.Progressed(a1) =>
    //         CrankRes.Progressed(WIP.Map(a1, f))
    //       case CrankRes.AlreadyIrreducible(w) =>
    //         w match
    //           case WIP.Irreducible.Done(value) =>
    //             ???
    //             // push `value` into `f`:
    //             //  - Done[A]
    //             //  - (Value[X], Action[X, Y], Promise[Y] => WIP[A])
    // }

  private enum CrankRes[A]:
    case AlreadyIrreducible(w: WIP.Irreducible[Action, Val, A])
    case Progressed(w: WIP[Action, Val, A])
}

private[runtime] object Processor {

  def start[Action[_, _], Val[_]](
    persistor: Persistor[Action, Val],
  )(using
    Unzippable[**, Val],
  ): Processor[Action, Val] = {
    val queue = new ArrayBlockingQueue[WorkItem](1000)
    val stopSignal = Promise[Unit]
    val processor = new Processor(persistor, queue, stopSignal)
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
