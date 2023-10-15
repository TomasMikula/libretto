package libretto.lambda.examples.workflow.generic.runtime

import libretto.lambda.Unzippable
import libretto.lambda.examples.workflow.generic.lang.{**, FlowAST, Workflows}

class WorkflowEngine[Action[_, _], Val[_]](
  worker: Worker[Action, Val],
)(using Unzippable[**, Val]) {
  val persistor = new Persistor[Action, Val]
  val processor = Processor.start(persistor, worker)

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
    processor.notify(WorkItem.Wakeup(ref))
    ref
  }

  def pollResult[A](ref: WorkflowRef[A]): Option[WorkflowResult[Val, A]] =
    persistor.pollResult(ref)
}

object WorkflowEngine {
  def start[Action[_, _], Val[_]](
    worker: Worker[Action, Val],
  )(using Unzippable[**, Val]): WorkflowEngine[Action, Val] =
    new WorkflowEngine[Action, Val](worker)
}
