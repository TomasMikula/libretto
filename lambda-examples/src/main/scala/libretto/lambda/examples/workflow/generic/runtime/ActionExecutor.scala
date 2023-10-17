package libretto.lambda.examples.workflow.generic.runtime

import java.util.concurrent.BlockingQueue
import scala.annotation.tailrec
import scala.util.Try

trait ActionExecutor[Action[_, _], Val[_]] {
  import ActionExecutor.*

  def submit[A, B](
    input: Value[Val, A],
    action: Action[A, B],
  )(
    onComplete: Try[Value[Val, B]] => Unit,
  ): Unit

  @tailrec
  final def consumeIndefinitely(q: BlockingQueue[ActionRequest[Action, Val]]): Unit =
    val req = q.take()
    submit(req.input, req.action)(req.onComplete)
    consumeIndefinitely(q)
}

object ActionExecutor {
  sealed trait ActionRequest[Action[_, _], Val[_]] {
    type In
    type Out
    def input: Value[Val, In]
    def action: Action[In, Out]
    def onComplete: Try[Value[Val, Out]] => Unit
  }
  object ActionRequest {
    case class Impl[Action[_, _], Val[_], A, B](
      override val input: Value[Val, A],
      override val action: Action[A, B],
      override val onComplete: Try[Value[Val, B]] => Unit,
    ) extends ActionRequest[Action, Val] {
      override type In = A
      override type Out = B
    }
  }

  def enqueuer[Action[_, _], Val[_]](
    queue: BlockingQueue[ActionRequest[Action, Val]],
  ): ActionExecutor[Action, Val] =
    new ActionExecutor[Action, Val] {
      override def submit[A, B](
        input: Value[Val, A],
        action: Action[A, B],
      )(
        onComplete: Try[Value[Val, B]] => Unit,
      ): Unit =
        queue.put(ActionRequest.Impl(input, action, onComplete))
    }
}
