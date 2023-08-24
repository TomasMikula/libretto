package libretto.lambda.examples.workflow.engine

import libretto.lambda.examples.workflow.lang.FlowAST

class WorkflowEngine[Action[_, _]] {

  def submit[A, B](
    workflow: FlowAST[Action, A, B],
    input: Value[A],
  ): WorkflowRef[B] =
    ???
}

object WorkflowEngine {
  def start[Action[_, _]](): WorkflowEngine[Action] =
    new WorkflowEngine[Action]
}
