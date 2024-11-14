package libretto.lambda.examples.workflow.generic.runtime

import libretto.lambda.{Capture, DistributionNAry, Focus, Knitted}
import libretto.lambda.examples.workflow.generic.lang.{**, ++, Enum, ||, ::}
import libretto.lambda.util.Exists

/** An action that might have already captured some of its inputs. */
enum RuntimeAction[Op[_, _], Val[_], A, B]:
  case DomainAction[Op[_, _], Val[_], A, B](
    f: Op[A, B],
  ) extends RuntimeAction[Op, Val, A, B]

  case ValueCollector[Op[_, _], Val[_], A, B](
    f: Capture[**, Value[Val, _], A, B],
  ) extends RuntimeAction[Op, Val, A, B]

  case DistLR[Op[_, _], Val[_], X, Y, Z](
    x: Value[Val, X],
  ) extends RuntimeAction[Op, Val, Y ++ Z, (X ** Y) ++ (X ** Z)]

  case DistLRNAry[Op[_, _], Val[_], A, Cases, ACases](
    a: Value[Val, A],
    d: DistributionNAry.DistLR[**, ||, ::, A, Cases] { type Out = ACases },
  ) extends RuntimeAction[Op, Val, Enum[Cases], Enum[ACases]]

object RuntimeAction {
  def action[Op[_, _], Val[_], A, B](f: Op[A, B]): RuntimeAction[Op, Val, A, B] =
    DomainAction(f)

  def captureValue[Op[_, _], Val[_], F[_], A](
    value: Value[Val, A],
    at: Focus.Proper[**, F],
  ): Exists[[F0] =>> (RuntimeAction[Op, Val, F0, F[A]], Knitted[**, F, F0])] =
    Capture.fromFocus(at, value) match
      case Exists.Some((f, k)) => Exists.Some((ValueCollector(f), k))
}
