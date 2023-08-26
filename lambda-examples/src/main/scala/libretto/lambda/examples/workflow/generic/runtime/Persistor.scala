package libretto.lambda.examples.workflow.generic.runtime

import libretto.lambda.examples.workflow.generic.lang.FlowAST
import scala.collection.mutable

private[runtime] class Persistor[Action[_, _], Val[_]] {
  private sealed trait Record[B] {
    def isReady: Boolean
  }

  private object Record {
    case class Active[A, B](
      cap: Cap[Val, A],
      tail: FlowAST[Action, A, B],
    ) extends Record[B] {
      override def isReady: Boolean = ???
    }
  }

  private var nextWorkflowId: Long = 1

  private val workflows: mutable.Map[WorkflowRef[?], Record[?]] =
    mutable.Map.empty[WorkflowRef[?], Record[?]]

  def insert[A, B](
    input: Value[Val, A],
    workflow: FlowAST[Action, A, B],
  ): WorkflowRef[B] =
    this.synchronized {
      val id = nextWorkflowId
      nextWorkflowId += 1
      val ref = WorkflowRef[B](id)
      val record = Record.Active(Cap.input(input), workflow)
      workflows.put(ref, record)
      ref
    }

  def pollWorkItem(): Option[WorkItem] =
    this.synchronized {
      workflows.collectFirst {
        case (ref, wf) if wf.isReady => WorkItem.InputReady(ref)
      }
    }
}
