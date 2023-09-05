package libretto.lambda.examples.workflow.generic.runtime

enum Promised[A]:
  case Empty()
  case Complete(value: A)
