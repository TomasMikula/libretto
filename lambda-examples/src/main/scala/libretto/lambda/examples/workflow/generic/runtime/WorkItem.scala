package libretto.lambda.examples.workflow.generic.runtime

enum WorkItem:
  case Wakeup(ref: WorkflowRef[?])
  case ReadingComplete(id: PortId[?])
  case TimerElapsed(ref: WorkflowRef[?], timer: TimerId)
