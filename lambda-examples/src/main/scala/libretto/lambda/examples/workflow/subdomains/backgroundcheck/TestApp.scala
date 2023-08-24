package libretto.lambda.examples.workflow.subdomains.backgroundcheck

import libretto.lambda.examples.workflow.engine.WorkflowEngine

object TestApp {
  def main(args: Array[String]): Unit =
    val engine = WorkflowEngine.start[Action]()

    val candidate = "john.doe@example.com"

    val ref = engine.submit(
      backgroundCheck,
      EmailAddress(candidate),
    )

    println(s"Started background check for $candidate: $ref")
}
