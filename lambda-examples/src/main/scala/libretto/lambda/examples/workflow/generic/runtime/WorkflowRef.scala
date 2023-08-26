package libretto.lambda.examples.workflow.generic.runtime

/** Reference to a workflow with output type `A` */
case class WorkflowRef[A] private[runtime] (value: Long)
