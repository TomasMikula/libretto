package libretto.lambda.examples.workflow.generic.runtime

import scala.util.Try

trait Worker[Action[_, _], Val[_]] {
  def executeAction[A, B](
    input: Value[Val, A],
    action: Action[A, B],
  )(
    onComplete: Try[Value[Val, B]] => Unit,
  ): Unit
}
