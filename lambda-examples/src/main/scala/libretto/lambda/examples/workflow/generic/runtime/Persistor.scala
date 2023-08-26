package libretto.lambda.examples.workflow.generic.runtime

import libretto.lambda.examples.workflow.generic.lang.FlowAST

private[runtime] class Persistor[Action[_, _], Val[_]] {
  def insert[A, B](input: Value[Val, A], workflow: FlowAST[Action, A, B]): WorkflowRef[B] =
    ???

  def pollWorkItem(): Option[WorkItem] =
    ???
}
