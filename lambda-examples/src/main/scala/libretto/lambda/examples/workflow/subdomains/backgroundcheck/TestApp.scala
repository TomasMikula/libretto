package libretto.lambda.examples.workflow.subdomains.backgroundcheck

import libretto.lambda.examples.workflow.generic.runtime.{ActionExecutor, WorkflowEngine}
import libretto.lambda.examples.workflow.generic.runtime.ActionExecutor.ActionRequest

import java.util.concurrent.ArrayBlockingQueue
import scala.annotation.tailrec
import java.util.concurrent.Executors

object TestApp {
  def main(args: Array[String]): Unit =
    val actionQueue =
      new ArrayBlockingQueue[ActionRequest[Action, Val]](1000)
    val scheduler =
      Executors.newSingleThreadScheduledExecutor()
    val engine =
      WorkflowEngine.start[Action, Val](ActionExecutor.enqueuer(actionQueue), scheduler)
    val actionExecutor =
      new DummyActionExecutor(engine)
    val execThread =
      forkDaemon(
        () => actionExecutor.consumeIndefinitely(actionQueue),
        threadName = "ActionExecutor",
      )

    val candidate = "john.doe@example.com"

    val ref = engine.submit(
      backgroundCheck,
      emailAddress(candidate),
    )

    println(s"Started background check for $candidate: $ref")

    @tailrec
    def go(): Unit =
      engine.pollResult(ref) match {
        case Some(res) =>
          println(s"Background check result: $res")
        case None =>
          println(s"Waiting for result")
          Thread.sleep(1000)
          go()
      }

    go()
    scheduler.shutdownNow()

  private def forkDaemon(
    body: () => Unit,
    threadName: String,
  ): Thread =
    val t = new Thread:
      override def run(): Unit = body()
    t.setName(threadName)
    t.setDaemon(true)
    t.setUncaughtExceptionHandler(((t, e) => e.printStackTrace(Console.err)))
    t.start()
    t
}
