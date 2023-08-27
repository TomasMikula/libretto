package libretto.lambda.examples.workflow.generic.runtime

import java.util.concurrent.{ArrayBlockingQueue, BlockingQueue, TimeUnit}
import scala.concurrent.{Future, Promise}
import java.lang.Thread.UncaughtExceptionHandler

private[runtime] class Processor[Action[_, _], Val[_]](
  persistor: Persistor[Action, Val],
  workQueue: BlockingQueue[WorkItem],
  stopSignal: Promise[Unit],
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
      case CrankRes.AlreadyStill(_) => None
      case CrankRes.Progressed(w1)  => Some(w1)

  private def crank[A](w: WIP[Action, Val, A]): CrankRes[A] =
    w match {
      case w: WIP.Still[Action, Val, A] =>
        // nothing to do, false alarm
        CrankRes.AlreadyStill(w)

      case WIP.Zip(a1, a2) =>
        println(w)
        ???

      case WIP.Map(a, f) =>
        println(w)
        ???
    }

  private enum CrankRes[A]:
    case AlreadyStill(w: WIP.Still[Action, Val, A])
    case Progressed(w: WIP[Action, Val, A])
}

private[runtime] object Processor {

  def start[Action[_, _], Val[_]](persistor: Persistor[Action, Val]): Processor[Action, Val] = {
    val queue = new ArrayBlockingQueue[WorkItem](1000)
    val stopSignal = Promise[Unit]
    val processor = new Processor(persistor, queue, stopSignal)
    val processorThread = new Thread {
      override def run(): Unit = processor.loop()
    }
    processorThread.setName("WorkflowProcessor")
    processorThread.setDaemon(true)
    processorThread.setUncaughtExceptionHandler((t, e) => { e.printStackTrace(Console.err); Console.err.flush() })
    processorThread.start()
    processor
  }

}
