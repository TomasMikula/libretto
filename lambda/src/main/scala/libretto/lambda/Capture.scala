package libretto.lambda

import libretto.lambda.util.{Exists, SourcePos}

sealed trait Capture[**[_, _], F[_], A, B] {
  import Capture.*

  def from[Z](using ev: Z =:= A): Capture[**, F, Z, B] =
    ev.substituteContra[Capture[**, F, _, B]](this)

  def to[C](using ev: B =:= C): Capture[**, F, A, C] =
    ev.substituteCo(this)

  def after[Z](that: Capture[**, F, Z, A])(using Unzippable[**, F]): Capture[**, F, Z, B]

  def >[C](that: Capture[**, F, B, C])(using Unzippable[**, F]): Capture[**, F, A, C] =
    that after this

  def inFst[Y]: Capture[**, F, A ** Y, B ** Y] =
    throw NotImplementedError(s"at ${summon[SourcePos]}")

  def inSnd[X]: Capture[**, F, X ** A, X ** B] =
    throw NotImplementedError(s"at ${summon[SourcePos]}")

  def complete(value: Tupled[**, F, A])(using Unzippable[**, F]): Tupled[**, F, B]

  def complete(value: F[A])(using Unzippable[**, F]): Tupled[**, F, B] =
    complete(Tupled.atom(value))

  def absorb[P[_], X](
    value: F[X],
    path: Focus.Proper[**, P],
  )(using P[X] =:= A, Unzippable[**, F]): Absorbed[**, F, P, B] =
    Capture.fromFocus(path, value) match
      case Exists.Some((f, k)) =>
        Absorbed.Impl(k, f.to[A] > this)
}

object Capture {
  case class NoCapture[**[_, _], F[_], A]() extends Capture[**, F, A, A]:
    override def complete(value: Tupled[**, F, A])(using Unzippable[**, F]): Tupled[**, F, A] =
      value

    override def after[Z](that: Capture[**, F, Z, A])(using Unzippable[**, F]): Capture[**, F, Z, A] =
      that

  sealed trait Proper[**[_, _], F[_], A, B] extends Capture[**, F, A, B]:
    override def after[Z](that: Capture[**, F, Z, A])(using Unzippable[**, F]): Capture.Proper[**, F, Z, B]

  case class CaptureFst[**[_, _], F[_], A, B1, B2](
    b1: Tupled[**, F, B1],
    f: Capture[**, F, A, B2],
  ) extends Proper[**, F, A, B1 ** B2]:
    override def complete(a: Tupled[**, F, A])(using Unzippable[**, F]): Tupled[**, F, B1 ** B2] =
      b1 zip f.complete(a)

    override def after[Z](that: Capture[**, F, Z, A])(using Unzippable[**, F]): Capture.Proper[**, F, Z, B1 ** B2] =
      CaptureFst(b1, that > f)

  case class CaptureSnd[**[_, _], F[_], A, B1, B2](
    f: Capture[**, F, A, B1],
    b2: Tupled[**, F, B2],
  ) extends Proper[**, F, A, B1 ** B2]:
    override def complete(a: Tupled[**, F, A])(using Unzippable[**, F]): Tupled[**, F, B1 ** B2] =
      f.complete(a) zip b2

    override def after[Z](that: Capture[**, F, Z, A])(using Unzippable[**, F]): Capture.Proper[**, F, Z, B1 ** B2] =
      CaptureSnd(that > f, b2)

  case class Par[**[_, _], F[_], A1, A2, B1, B2](
    f1: Proper[**, F, A1, B1],
    f2: Proper[**, F, A2, B2],
  ) extends Proper[**, F, A1 ** A2, B1 ** B2]:
    override def complete(value: Tupled[**, F, A1 ** A2])(using F: Unzippable[**, F]): Tupled[**, F, B1 ** B2] =
      val (a1, a2) = Tupled.unzip(value)
      f1.complete(a1) zip f2.complete(a2)

    override def after[Z](that: Capture[**, F, Z, A1 ** A2])(using Unzippable[**, F]): Capture.Proper[**, F, Z, B1 ** B2] =
      that match
        case NoCapture()       => this
        case CaptureFst(a1, h) => f1.complete(a1) match { case b1 => CaptureFst(b1, f2 after h) }
        case CaptureSnd(h, a2) => f2.complete(a2) match { case b2 => CaptureSnd(f1 after h, b2) }
        case Par(h1, h2)       => Par(f1 after h1, f2 after h2)

  def fromFocus[**[_, _], F[_], P[_], X](
    p: Focus.Proper[**, P],
    k: Knit[**, P[_]],
    x: F[X],
  ): Capture[**, F, k.Res, P[X]] =
    fromFocus(p, x) match
      case Exists.Some((res, k1)) =>
        Knitted.functional(k1, k).substituteCo[Capture[**, F, _, P[X]]](res)

  def fromFocus[**[_, _], F[_], P[_], X](
    p: Focus.Proper[**, P],
    x: F[X],
  ): Exists[[P0] =>> (Capture[**, F, P0, P[X]], Knitted[**, P, P0])] =
    p match
      case p: Focus.Fst[pr, p1, b] =>
        p.i match
          case Focus.Id() =>
            Exists((CaptureFst(Tupled.atom(x), NoCapture()), Knitted.keepSnd))
          case p1: Focus.Proper[pr, p1] =>
            fromFocus(p1, x) match
              case Exists.Some((capt, k)) =>
                Exists((capt.inFst[b], k.inFst[b]))
      case p: Focus.Snd[pr, p2, a] =>
        p.i match
          case Focus.Id() =>
            Exists((CaptureSnd(NoCapture(), Tupled.atom(x)), Knitted.keepFst))
          case p2: Focus.Proper[pr, p2] =>
            fromFocus(p2, x) match
              case Exists.Some((capt, k)) =>
                Exists((capt.inSnd[a], k.inSnd[a]))

  enum Absorbed[**[_, _], F[_], P[_], B]:
    case Impl[**[_, _], F[_], P[_], P0, B](
      knitted: Knitted[**, P, P0],
      result: Capture[**, F, P0, B],
    ) extends Absorbed[**, F, P, B]

    def inFst[Y]: Absorbed[**, F, [x] =>> P[x] ** Y, B ** Y] =
      this match { case Impl(k, r) => Impl(k.inFst, r.inFst) }

    def inSnd[X]: Absorbed[**, F, [x] =>> X ** P[x], X ** B] =
      this match { case Impl(k, r) => Impl(k.inSnd, r.inSnd) }
}
