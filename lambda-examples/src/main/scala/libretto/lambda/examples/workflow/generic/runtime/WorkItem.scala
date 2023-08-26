package libretto.lambda.examples.workflow.generic.runtime

enum WorkItem:
  case InputReady(ref: WorkflowRef[?])
