package libretto.lambda.examples.workflow.generic.runtime

enum WorkItem:
  case Wakeup(ref: WorkflowRef[?])