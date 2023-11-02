package libretto.lambda.examples.workflow.generic.runtime

import libretto.lambda.{Projection, Spine, UnhandledCase, Unzippable, Zippable}
import libretto.lambda.examples.workflow.generic.lang.{**, ++, PortName, Reading, given}
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

  def as[B](using ev: A =:= B): Input[Val, B] =
    ev.substituteCo(this)

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

  def supplyResult[X](
    pid: PortId[X],
    result: Value[Val, X],
  ): Option[Input[Val, A]] =
    this match
      case Ready(value) =>
        None
      case Awaiting(awaited) =>
        awaited.supplyResult(pid, result)
      case Zip(a1, a2) =>
        (a1.supplyResult(pid, result), a2.supplyResult(pid, result)) match
          case (None   , None   ) => None
          case (Some(i), None   ) => Some(Zip(i, a2))
          case (None   , Some(j)) => Some(Zip(a1, j))
          case (Some(i), Some(j)) => Some(Zip(i, j))

  def discard[B](p: Projection[**, A, B])(using Unzippable[**, Val]): Input[Val, B] =
    p match
      case Projection.Id() => this
      case p: Projection.Proper[**, A, B] => discardProper(p)

  private def discardProper[B](p: Projection.Proper[**, A, B])(using Unzippable[**, Val]): Input[Val, B] =
    this match
      case Ready(value) =>
        Ready(value.discardProper(p))
      case Awaiting(awaited) =>
        Awaiting(awaited.discardProper(p))
      case z: Zip[val_, a1, a2] =>
        p.fromPair[a1, a2].switch[Input[Val, B]](
          caseDiscardFst = p2 => z.a2.discard(p2),
          caseDiscardSnd = p1 => z.a1.discard(p1),
          casePar = [Q1, Q2] => (ev: B =:= (Q1 ** Q2)) ?=> (p: Projection.Par[**, a1, a2, Q1, Q2]) =>
            given ((Q1 ** Q2) =:= B) = ev.flip
            p match
              case Projection.Fst(p1) => Zip(z.a1.discardProper(p1), z.a2).as[B]
              case Projection.Snd(p2) => Zip(z.a1, z.a2.discardProper(p2)).as[B]
              case Projection.Both(p1, p2) => Zip(z.a1.discardProper(p1), z.a2.discardProper(p2)).as[B]
            ,
        )


  def **[B](that: Input[Val, B]): Input[Val, A ** B] =
    Zip(this, that)

  def isPartiallyReady: Boolean =
    this match
      case Ready(value)    => true
      case Awaiting(value) => false
      case Zip(a1, a2)     => a1.isPartiallyReady || a2.isPartiallyReady


object Input {
  def awaiting[Val[_], A](pa: PortId[A]): Input[Val, A] =
    Awaiting(AwaitedValues.Awaiting(pa))

  def awaitingTimeout[Val[_], A](pa: PortId[A], t: TimerId): Input[Val, A ++ Reading[A]] =
    Awaiting(AwaitedValues.AwaitingTimeout(pa, t))

  def portName[Val[_], A](pa: PortId[A]): Input[Val, PortName[A]] =
    Ready(Value.portName(pa))

  def reading[Val[_], A](pa: PortId[A]): Input[Val, Reading[A]] =
    Ready(Value.reading(pa))

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
  case Awaiting(promised: PortId[A])
  case AwaitingTimeout(promised: PortId[A], t: TimerId) extends AwaitedValues[Val, A ++ Reading[A]]
  case Zip[Val[_], A1, A2](
    a1: AwaitedValues[Val, A1],
    a2: AwaitedValues[Val, A2],
  ) extends AwaitedValues[Val, A1 ** A2]

  def **[B](that: AwaitedValues[Val, B]): AwaitedValues[Val, A ** B] =
    Zip(this, that)

  def supplyResult[X](
    px: PortId[X],
    result: Value[Val, X],
  ): Option[Input[Val, A]] =
    this match
      case Awaiting(pa) =>
        if (px == pa)
          Some(Input.Ready(result.asInstanceOf[Value[Val, A]]))
        else
          None
      case AwaitingTimeout(pa, t) =>
        if (px == pa)
          Some(Input.Ready(Value.left(result).asInstanceOf[Value[Val, A]]))
          // TODO: cancel the timer
        else
          None
      case Zip(a1, a2) =>
        (a1.supplyResult(px, result), a2.supplyResult(px, result)) match
          case (Some(i), Some(j)) => Some(Input.Zip(i, j))
          case (Some(i), None   ) => Some(Input.Zip(i, Input.Awaiting(a2)))
          case (None   , Some(j)) => Some(Input.Zip(Input.Awaiting(a1), j))
          case (None   , None   ) => None

  def discardProper[B](p: Projection.Proper[**, A, B]): AwaitedValues[Val, B] =
    UnhandledCase.raise(s"AwaitedValues.discardProper($p)")
