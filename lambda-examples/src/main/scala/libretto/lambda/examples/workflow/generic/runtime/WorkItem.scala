package libretto.lambda.examples.workflow.generic.runtime

enum WorkItem:
  case Wakeup(ref: WorkflowRef[?])
  case PromiseCompleted(id: PromiseId[?])
  case TimerElapsed(ref: WorkflowRef[?], timer: TimerId)
