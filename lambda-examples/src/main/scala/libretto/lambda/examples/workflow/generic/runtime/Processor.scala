package libretto.lambda.examples.workflow.generic.runtime

import java.util.concurrent.{ArrayBlockingQueue, BlockingQueue, TimeUnit}
import scala.concurrent.{Future, Promise}

private[runtime] class Processor[Action[_, _], Val[_]](
  persistor: Persistor[Action, Val],
  workQueue: BlockingQueue[WorkItem],
  stopSignal: Promise[Unit],
) {
  def notify(item: WorkItem): Unit =
    workQueue.put(item)
}

private[runtime] object Processor {

  def start[Action[_, _], Val[_]](persistor: Persistor[Action, Val]): Processor[Action, Val] = {
    val queue = new ArrayBlockingQueue[WorkItem](1000)
    val stopSignal = Promise[Unit]
    val processor = new Processor(persistor, queue, stopSignal)
    new Thread {
      override def run(): Unit = processLoop(persistor, queue, stopSignal.future)
    }.run()
    processor
  }

  private def processLoop[Action[_, _], Val[_]](
    persistor: Persistor[Action, Val],
    workQueue: BlockingQueue[WorkItem],
    stopSignal: Future[Unit],
  ): Unit = {
    def poll(): Option[WorkItem] =
      Option(workQueue.poll())
        .orElse(persistor.pollWorkItem())
        .orElse(Option(workQueue.poll(5, TimeUnit.SECONDS)))

    while (!stopSignal.isCompleted) {
      poll()
        .foreach { processItem(persistor, _) }
    }
  }

  private def processItem[Action[_, _], Val[_]](
    persistor: Persistor[Action, Val],
    item: WorkItem,
  ): Unit =
    println(s"processItem($item)")
    ???
}
