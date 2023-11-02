package libretto.lambda.examples.workflow.generic.runtime

enum InputPortState[Val[_], A]:
  case Empty()
  case Completed(value: Value[Val, A])
