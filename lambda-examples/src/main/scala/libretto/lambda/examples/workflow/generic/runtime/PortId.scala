package libretto.lambda.examples.workflow.generic.runtime

sealed trait PortId[A]:
  type WorkflowResult
  def workflow: WorkflowRef[WorkflowResult]

object PortId:
  case class Impl[W, A](
    workflow: WorkflowRef[W],
    value: Long,
  ) extends PortId[A]:
    override type WorkflowResult = W

  def apply[A](w: WorkflowRef[?], value: Long): PortId[A] =
    Impl(w, value)