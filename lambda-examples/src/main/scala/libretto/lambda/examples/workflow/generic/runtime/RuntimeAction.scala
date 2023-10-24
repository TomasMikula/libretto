package libretto.lambda.examples.workflow.generic.runtime

import libretto.lambda.Capture
import libretto.lambda.examples.workflow.generic.lang.{**, ++}

/** An action that might have already captured some of its inputs. */
enum RuntimeAction[Op[_, _], Val[_], A, B]:
  case DomainAction[Op[_, _], Val[_], A, X, B](
    args: Capture[**, Value[Val, _], A, X],
    f: Op[X, B],
  ) extends RuntimeAction[Op, Val, A, B]
  case DistLR[Op[_, _], Val[_], X, Y, Z](
    x: Value[Val, X],
  ) extends RuntimeAction[Op, Val, Y ++ Z, (X ** Y) ++ (X ** Z)]

object RuntimeAction {
  def action[Op[_, _], Val[_], A, B](f: Op[A, B]): RuntimeAction[Op, Val, A, B] =
    DomainAction(Capture.NoCapture(), f)

  def partiallyApplied[Op[_, _], Val[_], A, X, B](
    args: Capture[**, Value[Val, _], A, X],
    f: Op[X, B],
  ): RuntimeAction[Op, Val, A, B] =
    DomainAction(args, f)
}
