package libretto.lambda.examples.workflow.generic.runtime

enum PromiseState[A]:
  case Empty()
  case Complete(value: A)
