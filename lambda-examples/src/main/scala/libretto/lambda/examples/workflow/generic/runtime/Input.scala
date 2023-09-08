package libretto.lambda.examples.workflow.generic.runtime

import libretto.lambda.Spine
import libretto.lambda.examples.workflow.generic.lang.**


enum Input[Val[_], A]:
  import Input.*

  case Ready(value: Value[Val, A])
  case Awaiting(value: AwaitedValues[Val, A])
  case Zip[Val[_], A1, A2](
    a1: Input[Val, A1],
    a2: Input[Val, A2],
  ) extends Input[Val, A1 ** A2]

  def findValue: FindValueRes[Val, A] =
    import FindValueRes.*

    this match
      case Ready(value) => ???
      case Awaiting(value) => ???
      case Zip(a1, a2) => ???


object Input {
  enum FindValueRes[Val[_], A]:
    case NotFound(awaiting: AwaitedValues[Val, A])
    case Found[Val[_], F[_], X, A](
      path: Spine[**, Input[Val, _], F],
      value: Value[Val, X],
      ev: F[X] =:= A,
    ) extends FindValueRes[Val, A]
}

enum AwaitedValues[Val[_], A]:
  case Awaiting(promised: PromiseId[A])
  case Zip[Val[_], A1, A2](
    a1: AwaitedValues[Val, A1],
    a2: AwaitedValues[Val, A2],
  ) extends AwaitedValues[Val, A1 ** A2]

