package libretto.lambda.examples.workflow.generic.runtime

import libretto.lambda.examples.workflow.generic.lang.{FlowAST, Workflows}

class WorkflowEngine[Action[_, _]] {
  def submit[A, B](using ws: Workflows[Action])(
    workflow: ws.Flow[A, B],
    input: Value[A],
  ): WorkflowRef[B] =
    submitAST(ws.astOf(workflow), input)

  def submitAST[A, B](
    workflow: FlowAST[Action, A, B],
    input: Value[A],
  ): WorkflowRef[B] =
    ???
}

object WorkflowEngine {
  def start[Action[_, _]](): WorkflowEngine[Action] =
    new WorkflowEngine[Action]
}
