package libretto.lambda

import libretto.lambda.util.{Exists, SourcePos, TypeEq}
import libretto.lambda.util.TypeEq.Refl

sealed trait Capture[**[_, _], F[_], A, B] {
  import Capture.*

  def from[Z](using ev: Z =:= A): Capture[**, F, Z, B] =
    ev.substituteContra[Capture[**, F, _, B]](this)

  def to[C](using ev: B =:= C): Capture[**, F, A, C] =
    ev.substituteCo(this)

  def after[Z](that: Capture[**, F, Z, A])(using Unzippable[**, F]): Capture[**, F, Z, B]

  def >[C](that: Capture[**, F, B, C])(using Unzippable[**, F]): Capture[**, F, A, C] =
    that after this

  def inFst[Y]: Capture[**, F, A ** Y, B ** Y]

  def inSnd[X]: Capture[**, F, X ** A, X ** B]

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

  def exposeCaptured(using sh: Shuffle[**]): Either[A =:= B, Capture.Exposed[sh.type, **, F, A, B]] =
    this match
      case NoCapture() => Left(summon[A =:= B])
      case CaptureFst(b1, f) =>
        f.exposeCaptured match
          case Left(TypeEq(Refl())) => Right(Capture.Exposed(b1, sh.TransferOpt.None()))
          case Right(exp)           => Right(exp.alsoCaptureFst(b1))
      case CaptureSnd(f, b2) =>
        UnhandledCase.raise(s"$this.exposeCaptured")
      case InFst(f) =>
        UnhandledCase.raise(s"$this.exposeCaptured")
      case InSnd(f) =>
        UnhandledCase.raise(s"$this.exposeCaptured")
      case Par(f1, f2) =>
        UnhandledCase.raise(s"$this.exposeCaptured")

}

object Capture {
  case class NoCapture[**[_, _], F[_], A]() extends Capture[**, F, A, A]:
    override def complete(value: Tupled[**, F, A])(using Unzippable[**, F]): Tupled[**, F, A] =
      value

    override def after[Z](that: Capture[**, F, Z, A])(using Unzippable[**, F]): Capture[**, F, Z, A] =
      that

    override def inFst[Y]: Capture[**, F, A ** Y, A ** Y] =
      NoCapture()

    override def inSnd[X]: Capture[**, F, X ** A, X ** A] =
      NoCapture()

  sealed trait Proper[**[_, _], F[_], A, B] extends Capture[**, F, A, B]:
    override def after[Z](that: Capture[**, F, Z, A])(using Unzippable[**, F]): Capture.Proper[**, F, Z, B]

    override def inFst[Y]: Capture[**, F, A ** Y, B ** Y] =
      Capture.InFst(this)

    override def inSnd[X]: Capture[**, F, X ** A, X ** B] =
      Capture.InSnd(this)

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

  case class InFst[**[_, _], F[_], A, B, Y](
    f: Capture.Proper[**, F, A, B],
  ) extends Proper[**, F, A ** Y, B ** Y]:
    override def complete(value: Tupled[**, F, A ** Y])(using F: Unzippable[**, F]): Tupled[**, F, B ** Y] =
      val (a, y) = Tupled.unzip(value)
      f.complete(a) zip y

    override def after[Z](that: Capture[**, F, Z, A ** Y])(using Unzippable[**, F]): Proper[**, F, Z, B ** Y] =
      that match
        case NoCapture()       => this
        case CaptureFst(b1, g) => CaptureFst(f.complete(b1), g)
        case CaptureSnd(g, b2) => CaptureSnd(f after g, b2)
        case InFst(g)          => InFst(f after g).asInstanceOf // XXX
        case InSnd(g)          => Par(f, g)
        case Par(g1, g2)       => Par(f after g1, g2)


  case class InSnd[**[_, _], F[_], X, A, B](
    f: Capture.Proper[**, F, A, B],
  ) extends Proper[**, F, X ** A, X ** B]:
    override def complete(value: Tupled[**, F, X ** A])(using F: Unzippable[**, F]): Tupled[**, F, X ** B] =
      val (x, a) = Tupled.unzip(value)
      x zip f.complete(a)

    override def after[Z](that: Capture[**, F, Z, X ** A])(using Unzippable[**, F]): Proper[**, F, Z, X ** B] =
      that match
        case NoCapture()       => this
        case CaptureFst(b1, g) => CaptureFst(b1, f after g)
        case CaptureSnd(g, b2) => CaptureSnd(g, f.complete(b2))
        case InFst(g)          => Par(g, f)
        case InSnd(g)          => InSnd(f after g).asInstanceOf // XXX
        case Par(g1, g2)       => Par(g1, f after g2)


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
        case CaptureFst(a1, h) => CaptureFst(f1.complete(a1), f2 after h)
        case CaptureSnd(h, a2) => CaptureSnd(f1 after h, f2.complete(a2))
        case InFst(h)          => Par(f1 after h, f2)
        case InSnd(h)          => Par(f1, f2 after h)
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

  sealed trait Exposed[Sh <: Shuffle[**], **[_, _], F[_], A, B]:
    type X
    type Y1
    type Y2
    given ev: ((Y1 ** Y2) =:= B)
    val shuffle: Sh
    def captured: Tupled[**, F, X]
    def route: shuffle.TransferOpt[X, A, Y1, Y2]

    def alsoCaptureFst[P](p: Tupled[**, F, P]): Exposed[Sh, **, F, A, P ** B]

  object Exposed:
    def apply[**[_, _], F[_], P, A, B1, B2](using
      sh: Shuffle[**],
    )(
      capt: Tupled[**, F, P],
      rout: sh.TransferOpt[P, A, B1, B2],
    ): Exposed[sh.type, **, F, A, B1 ** B2] =
      new Exposed[sh.type, **, F, A, B1 ** B2]:
        override type X = P
        override type Y1 = B1
        override type Y2 = B2
        override def ev: (Y1 ** Y2) =:= (B1 ** B2) = summon
        override val shuffle = sh
        override def captured = capt
        override def route = rout

        override def alsoCaptureFst[P](p: Tupled[**, F, P]): Exposed[sh.type, **, F, A, P ** (B1 ** B2)] =
          Exposed(using shuffle)(
            p zip captured,
            shuffle.Transfer.AssocLR(route)
          )
}
