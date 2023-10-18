package libretto.lambda.examples.workflow.generic.runtime

sealed trait PromiseId[A]:
  type WorkflowResult
  def workflow: WorkflowRef[WorkflowResult]

object PromiseId:
  case class Impl[W, A](
    workflow: WorkflowRef[W],
    value: Long,
  ) extends PromiseId[A]:
    override type WorkflowResult = W

  def apply[A](w: WorkflowRef[?], value: Long): PromiseId[A] =
    Impl(w, value)