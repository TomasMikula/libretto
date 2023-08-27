package libretto.lambda.examples.workflow.generic.runtime

enum WorkflowResult[Val[_], A] {
  case Success(value: Value[Val, A])
}
