package libretto.lambda.examples.workflow.generic.runtime

import libretto.lambda.examples.workflow.generic.lang.{FlowAST, Workflows}

class WorkflowEngine[Action[_, _], Val[_]] {
  val persistor = new Persistor[Action, Val]
  val processor = Processor.start(persistor)

  def submit[A, B](using ws: Workflows[Action])(
    workflow: ws.Flow[A, B],
    input: Value[Val, A],
  ): WorkflowRef[B] =
    submitAST(ws.astOf(workflow), input)

  def submitAST[A, B](
    workflow: FlowAST[Action, A, B],
    input: Value[Val, A],
  ): WorkflowRef[B] = {
    val ref = persistor.insert(input, workflow)
    processor.notify(WorkItem.InputReady(ref))
    ref
  }
}

object WorkflowEngine {
  def start[Action[_, _], Val[_]](): WorkflowEngine[Action, Val] =
    new WorkflowEngine[Action, Val]
}
