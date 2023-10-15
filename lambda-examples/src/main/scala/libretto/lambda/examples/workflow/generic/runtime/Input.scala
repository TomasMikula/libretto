package libretto.lambda.examples.workflow.generic.runtime

import libretto.lambda.{Spine, Zippable}
import libretto.lambda.examples.workflow.generic.lang.**
import libretto.lambda.util.TypeEq
import libretto.lambda.util.TypeEq.{Refl, *}

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
      case Ready(value) =>
        Found(Spine.Id(), value, summon)
      case Awaiting(value) =>
        NotFound(value)
      case z: Zip[v, a1, a2] =>
        z.a1.findValue match
          case NotFound(awaiting1) =>
            z.a2.findValue match
              case NotFound(awaiting2) =>
                NotFound(awaiting1 ** awaiting2)
              case Found(path, value, ev) =>
                Found(path.inSnd(z.a1), value, ev.inSnd)
          case Found(path, value, ev) =>
            Found(path.inFst(z.a2), value, ev.inFst)

  def **[B](that: Input[Val, B]): Input[Val, A ** B] =
    Zip(this, that)

  def isPartiallyReady: Boolean =
    this match
      case Ready(value)    => true
      case Awaiting(value) => false
      case Zip(a1, a2)     => a1.isPartiallyReady || a2.isPartiallyReady


object Input {
  def awaiting[Val[_], A](pa: PromiseId[A]): Input[Val, A] =
    Awaiting(AwaitedValues.Awaiting(pa))

  enum FindValueRes[Val[_], A]:
    case NotFound(awaiting: AwaitedValues[Val, A])
    case Found[Val[_], F[_], X, A](
      path: Spine[**, Input[Val, _], F],
      value: Value[Val, X],
      ev: F[X] =:= A,
    ) extends FindValueRes[Val, A]

  given zippableInput[Val[_]]: Zippable[**, Input[Val, _]] with
    override def zip[A, B](fa: Input[Val, A], fb: Input[Val, B]): Input[Val, A ** B] =
      Input.Zip(fa, fb)
}

enum AwaitedValues[Val[_], A]:
  case Awaiting(promised: PromiseId[A])
  case Zip[Val[_], A1, A2](
    a1: AwaitedValues[Val, A1],
    a2: AwaitedValues[Val, A2],
  ) extends AwaitedValues[Val, A1 ** A2]

  def **[B](that: AwaitedValues[Val, B]): AwaitedValues[Val, A ** B] =
    Zip(this, that)

