package libretto.lambda.examples.workflow.generic.runtime

enum WorkItem:
  case Wakeup(ref: WorkflowRef[?])
  case ReadingComplete(workflow: WorkflowRef[?], id: PortId[?])
  case ActionComplete(workflow: WorkflowRef[?], id: ActionRunId[?])
  case TimerElapsed(ref: WorkflowRef[?], timer: TimerId)
