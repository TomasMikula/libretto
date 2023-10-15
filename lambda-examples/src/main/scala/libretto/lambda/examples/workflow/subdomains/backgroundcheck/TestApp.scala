package libretto.lambda.examples.workflow.subdomains.backgroundcheck

import libretto.lambda.examples.workflow.generic.runtime.WorkflowEngine
import scala.annotation.tailrec

object TestApp {
  def main(args: Array[String]): Unit =
    val engine = WorkflowEngine.start[Action, Val](new ActionExecutor)

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
          println(res)
        case None =>
          println(s"Waiting for result")
          Thread.sleep(1000)
          go()
      }

    go()
}
