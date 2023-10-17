package libretto.lambda.examples.workflow.generic.runtime

import libretto.lambda.Unzippable
import libretto.lambda.examples.workflow.generic.lang.{**, FlowAST, Workflows}

import scala.util.Try

class WorkflowEngine[Action[_, _], Val[_]](
  worker: ActionExecutor[Action, Val],
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

  def completePromise[A](p: PromiseId[A], result: Try[Value[Val, A]]): Boolean =
    if (persistor.completePromise(p, result))
      processor.notify(WorkItem.PromiseCompleted(p))
      true
    else
      false

  def pollResult[A](ref: WorkflowRef[A]): Option[WorkflowResult[Val, A]] =
    persistor.pollResult(ref)
}

object WorkflowEngine {
  def start[Action[_, _], Val[_]](
    worker: ActionExecutor[Action, Val],
  )(using Unzippable[**, Val]): WorkflowEngine[Action, Val] =
    new WorkflowEngine[Action, Val](worker)
}
