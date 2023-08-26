package libretto.lambda.examples.workflow.subdomains.backgroundcheck

import libretto.lambda.examples.workflow.generic.runtime.WorkflowEngine

object TestApp {
  def main(args: Array[String]): Unit =
    val engine = WorkflowEngine.start[Action, Val]()

    val candidate = "john.doe@example.com"

    val ref = engine.submit(
      backgroundCheck,
      emailAddress(candidate),
    )

    println(s"Started background check for $candidate: $ref")
}
