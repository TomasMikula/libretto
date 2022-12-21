package libretto.lambda

import libretto.util.{BiInjective, TypeEq}
import libretto.util.TypeEq.Refl

sealed trait Projection[|*|[_, _], P, Q] {
  def at[F[_]](f: Focus[|*|, F]): Projection[|*|, F[P], F[Q]]

  def >[R](that: Projection[|*|, Q, R]): Projection[|*|, P, R]

  def from[O](using ev: O =:= P): Projection[|*|, O, Q] =
    ev.substituteContra[[p] =>> Projection[|*|, p, Q]](this)

  def to[R](using ev: Q =:= R): Projection[|*|, P, R] =
    ev.substituteCo(this)
}

object Projection {
  case class Id[|*|[_, _], P]() extends Projection[|*|, P, P] {
    override def at[F[_]](f: Focus[|*|, F]): Projection[|*|, F[P], F[P]] = Id()
    override def >[R](that: Projection[|*|, P, R]): Projection[|*|, P, R] = that
  }

  sealed trait Proper[|*|[_, _], P, Q] extends Projection[|*|, P, Q] {
    override def at[F[_]](f: Focus[|*|, F]): Projection.Proper[|*|, F[P], F[Q]] =
      f match {
        case Focus.Id()    => this
        case Focus.Fst(f1) => Fst(this.at(f1))
        case Focus.Snd(f2) => Snd(this.at(f2))
      }

    override def >[R](that: Projection[|*|, Q, R]): Proper[|*|, P, R] = ???

    def fromPair[P1, P2](using P =:= (P1 |*| P2)): FromPair[P1, P2] =
      FromPair[P1, P2]

    class FromPair[P1, P2](using ev: P =:= (P1 |*| P2)) {
      def switch[R](
        caseDiscardFst: (p2: Projection[|*|, P2, Q]) => R,
        caseDiscardSnd: (p1: Projection[|*|, P1, Q]) => R,
        casePar: [Q1, Q2] => (Q =:= (Q1 |*| Q2)) ?=> (p: Par[|*|, P1, P2, Q1, Q2]) => R,
      )(using BiInjective[|*|]): R =
        switchFromPair[P1, P2, R](caseDiscardFst, caseDiscardSnd, casePar)
    }

    def switchFromPair[P1, P2, R](using ev: P =:= (P1 |*| P2))(
      caseDiscardFst: (p2: Projection[|*|, P2, Q]) => R,
      caseDiscardSnd: (p1: Projection[|*|, P1, Q]) => R,
      casePar: [Q1, Q2] => (Q =:= (Q1 |*| Q2)) ?=> (p: Par[|*|, P1, P2, Q1, Q2]) => R,
    )(using BiInjective[|*|]): R =
      this match {
        case p: DiscardFst[|*|, p1, p2, q] =>
          summon[(p1 |*| p2) =:= (P1 |*| P2)] match
            case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
              caseDiscardFst(p.p2)
        case p: DiscardSnd[|*|, p1, p2, q] =>
          summon[(p1 |*| p2) =:= (P1 |*| P2)] match
            case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
              caseDiscardSnd(p.p1)
        case p: Par[|*|, p1, p2, q1, q2] =>
          summon[(p1 |*| p2) =:= (P1 |*| P2)] match
            case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
              casePar[q1, q2](p)
      }
  }

  case class DiscardFst[|*|[_, _], A, B, B0](p2: Projection[|*|, B, B0]) extends Proper[|*|, A |*| B, B0]
  case class DiscardSnd[|*|[_, _], A, B, A0](p1: Projection[|*|, A, A0]) extends Proper[|*|, A |*| B, A0]

  sealed trait Par[|*|[_, _], P1, P2, Q1, Q2] extends Proper[|*|, P1 |*| P2, Q1 |*| Q2] {
    def unpar: (Projection[|*|, P1, Q1], Projection[|*|, P2, Q2]) =
      this match {
        case Fst(p1)      => (p1, Id())
        case Snd(p2)      => (Id(), p2)
        case Both(p1, p2) => (p1, p2)
      }
  }
  case class Fst[|*|[_, _], P, Q, B](p1: Proper[|*|, P, Q]) extends Par[|*|, P, B, Q, B]
  case class Snd[|*|[_, _], A, P, Q](p2: Proper[|*|, P, Q]) extends Par[|*|, A, P, A, Q]
  case class Both[|*|[_, _], P1, P2, Q1, Q2](p1: Proper[|*|, P1, Q1], p2: Proper[|*|, P2, Q2]) extends Par[|*|, P1, P2, Q1, Q2]

  def id[|*|[_, _], P]: Projection[|*|, P, P] = Id()
  def discardFst[|*|[_, _], A, B, B0](p2: Projection[|*|, B, B0]): Proper[|*|, A |*| B, B0] = DiscardFst(p2)
  def discardSnd[|*|[_, _], A, B, A0](p1: Projection[|*|, A, A0]): Proper[|*|, A |*| B, A0] = DiscardSnd(p1)
  def discardFst[|*|[_, _], A, B]: Proper[|*|, A |*| B, B] = DiscardFst(Id())
  def discardSnd[|*|[_, _], A, B]: Proper[|*|, A |*| B, A] = DiscardSnd(Id())

  def fst[|*|[_, _], P, Q, B](p1: Projection[|*|, P, Q]): Projection[|*|, P |*| B, Q |*| B] =
    p1 match
      case Id()                  => Id()
      case p1: Proper[|*|, p, q] => Fst(p1)

  def snd[|*|[_, _], A, P, Q](p2: Projection[|*|, P, Q]): Projection[|*|, A |*| P, A |*| Q] =
    p2 match
      case Id()                  => Id()
      case p2: Proper[|*|, p, q] => Snd(p2)

  def par[|*|[_, _], P1, P2, Q1, Q2](p1: Projection[|*|, P1, Q1], p2: Projection[|*|, P2, Q2]): Projection[|*|, P1 |*| P2, Q1 |*| Q2] =
    (p1, p2) match {
      case (Id(), p2) => snd(p2)
      case (p1, Id()) => fst(p1)
      case (p1: Proper[|*|, p1, q1], p2: Proper[|*|, p2, q2]) => Both(p1, p2)
    }

  def par1[|*|[_, _], P1, P2, Q1, Q2](p1: Proper[|*|, P1, Q1], p2: Projection[|*|, P2, Q2]): Proper[|*|, P1 |*| P2, Q1 |*| Q2] =
    p2 match {
      case Id() => Fst(p1)
      case p2: Proper[|*|, p2, q2] => Both(p1, p2)
    }

  def par2[|*|[_, _], P1, P2, Q1, Q2](p1: Projection[|*|, P1, Q1], p2: Proper[|*|, P2, Q2]): Proper[|*|, P1 |*| P2, Q1 |*| Q2] =
    p1 match {
      case Id() => Snd(p2)
      case p1: Proper[|*|, p1, q1] => Both(p1, p2)
    }
}
