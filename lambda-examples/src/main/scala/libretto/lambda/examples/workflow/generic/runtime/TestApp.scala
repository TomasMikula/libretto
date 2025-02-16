package libretto.lambda.examples.workflow.generic.runtime

import libretto.lambda.examples.workflow.generic.lang.Workflows
import libretto.lambda.examples.workflow.generic.runtime.ActionExecutor.ActionRequest

import java.util.concurrent.ArrayBlockingQueue
import scala.annotation.tailrec
import java.util.concurrent.Executors

class TestApp[Action[_, _], Val[_], A, B](using ws: Workflows[Action], v: Value.Compliant[Val])(
  actionExecutorFactory: WorkflowEngine[Action, Val] => ActionExecutor[Action, Val],
  input: Value[Val, A],
  workflow: ws.Flow[A, B],
) {
  def main(args: Array[String]): Unit =
    val actionQueue =
      new ArrayBlockingQueue[ActionRequest[Action, Val]](1000)
    val scheduler =
      Executors.newSingleThreadScheduledExecutor()
    val engine =
      WorkflowEngine.start[Action, Val](ActionExecutor.enqueuer(actionQueue), scheduler)
    val actionExecutor =
      actionExecutorFactory(engine)
    val execThread =
      forkDaemon(
        () => actionExecutor.consumeIndefinitely(actionQueue),
        threadName = "ActionExecutor",
      )

    val ref = engine.submit(workflow, input)

    println(s"Started workflow with input $input: $ref")

    @tailrec
    def go(): Unit =
      engine.pollResult(ref) match {
        case Some(res) =>
          println(s"Workflow result: $res")
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
