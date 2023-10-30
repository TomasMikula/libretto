package libretto.lambda

import libretto.lambda.util.{BiInjective, Exists, TypeEq}
import libretto.lambda.util.TypeEq.Refl

sealed trait Projection[|*|[_, _], P, Q] {
  def at[F[_]](f: Focus[|*|, F]): Projection[|*|, F[P], F[Q]]

  def >[R](that: Projection[|*|, Q, R]): Projection[|*|, P, R]

  def inFst[Y]: Projection[|*|, P |*| Y, Q |*| Y]

  def inSnd[X]: Projection[|*|, X |*| P, X |*| Q]

  def from[O](using ev: O =:= P): Projection[|*|, O, Q] =
    ev.substituteContra[[p] =>> Projection[|*|, p, Q]](this)

  def to[R](using ev: Q =:= R): Projection[|*|, P, R] =
    ev.substituteCo(this)
}

object Projection {
  case class Id[|*|[_, _], P]() extends Projection[|*|, P, P] {
    override def at[F[_]](f: Focus[|*|, F]): Projection[|*|, F[P], F[P]] = Id()
    override def >[R](that: Projection[|*|, P, R]): Projection[|*|, P, R] = that
    override def inFst[Y]: Projection[|*|, P |*| Y, P |*| Y] = Id()
    override def inSnd[X]: Projection[|*|, X |*| P, X |*| P] = Id()
  }

  sealed trait Proper[|*|[_, _], P, Q] extends Projection[|*|, P, Q] {
    override def at[F[_]](f: Focus[|*|, F]): Projection.Proper[|*|, F[P], F[Q]] =
      f match {
        case Focus.Id()    => this
        case Focus.Fst(f1) => Fst(this.at(f1))
        case Focus.Snd(f2) => Snd(this.at(f2))
      }

    override def >[R](that: Projection[|*|, Q, R]): Proper[|*|, P, R] =
      that match {
        case Id() => this
        case p: DiscardFst[pair, q1, q2, r] => discardFst[q1, q2] > p.p2
        case p: DiscardSnd[pair, q1, q2, r] => discardSnd[q1, q2] > p.p1
        case p: Fst[pair, q1, r1, q2]       => projectFst[q1, q2, r1](p.p1)
        case p: Snd[pair, q1, q2, r2]       => projectSnd[q1, q2, r2](p.p2)
        case p: Both[pair, q1, q2, r1, r2]  => projectFst[q1, q2, r1](p.p1) > p.p2.inSnd
      }

    override def from[O](using ev: O =:= P): Proper[|*|, O, Q] =
      ev.substituteContra[[p] =>> Proper[|*|, p, Q]](this)

    override def to[R](using ev: Q =:= R): Proper[|*|, P, R] =
      ev.substituteCo(this)

    protected def discardFst[Q1, Q2](using ev: Q =:= (Q1 |*| Q2)): Proper[|*|, P, Q2]

    protected def discardSnd[Q1, Q2](using ev: Q =:= (Q1 |*| Q2)): Proper[|*|, P, Q1]

    protected def projectFst[Q1, Q2, R1](using ev: Q =:= (Q1 |*| Q2))(p1: Proper[|*|, Q1, R1]): Proper[|*|, P, R1 |*| Q2]

    protected def projectSnd[Q1, Q2, R2](using ev: Q =:= (Q1 |*| Q2))(p2: Proper[|*|, Q2, R2]): Proper[|*|, P, Q1 |*| R2]

    override def inFst[X2]: Proper[|*|, P |*| X2, Q |*| X2] =
      Fst(this)

    override def inSnd[X1]: Proper[|*|, X1 |*| P, X1 |*| Q] =
      Snd(this)

    def startsFromPair: Exists[[P1] =>> Exists[[P2] =>> P =:= (P1 |*| P2)]]

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

  case class DiscardFst[|*|[_, _], A, B, B0](p2: Projection[|*|, B, B0]) extends Proper[|*|, A |*| B, B0] {
    override def startsFromPair: Exists[[P1] =>> Exists[[P2] =>> (A |*| B) =:= (P1 |*| P2)]] =
      Exists(Exists(summon))

    override protected def discardFst[Q1, Q2](using ev: B0 =:= (Q1 |*| Q2)): Proper[|*|, A |*| B, Q2] = ???
    override protected def discardSnd[Q1, Q2](using ev: B0 =:= (Q1 |*| Q2)): Proper[|*|, A |*| B, Q1] = ???
    override protected def projectFst[Q1, Q2, R1](using ev: B0 =:= (Q1 |*| Q2))(p1: Proper[|*|, Q1, R1]): Proper[|*|, A |*| B, R1 |*| Q2] = ???
    override protected def projectSnd[Q1, Q2, R2](using ev: B0 =:= (Q1 |*| Q2))(p2: Proper[|*|, Q2, R2]): Proper[|*|, A |*| B, Q1 |*| R2] = ???
  }

  case class DiscardSnd[|*|[_, _], A, B, A0](p1: Projection[|*|, A, A0]) extends Proper[|*|, A |*| B, A0] {
    override def startsFromPair: Exists[[P1] =>> Exists[[P2] =>> (A |*| B) =:= (P1 |*| P2)]] =
      Exists(Exists(summon))

    override protected def discardFst[Q1, Q2](using ev: A0 =:= (Q1 |*| Q2)): Proper[|*|, A |*| B, Q2] = ???
    override protected def discardSnd[Q1, Q2](using ev: A0 =:= (Q1 |*| Q2)): Proper[|*|, A |*| B, Q1] = ???
    override protected def projectFst[Q1, Q2, R1](using ev: A0 =:= (Q1 |*| Q2))(p1: Proper[|*|, Q1, R1]): Proper[|*|, A |*| B, R1 |*| Q2] = ???
    override protected def projectSnd[Q1, Q2, R2](using ev: A0 =:= (Q1 |*| Q2))(p2: Proper[|*|, Q2, R2]): Proper[|*|, A |*| B, Q1 |*| R2] = ???
  }

  sealed trait Par[|*|[_, _], P1, P2, Q1, Q2] extends Proper[|*|, P1 |*| P2, Q1 |*| Q2] {
    override def startsFromPair: Exists[[X1] =>> Exists[[X2] =>> (P1 |*| P2) =:= (X1 |*| X2)]] =
      Exists(Exists(summon))

    def unpar: (Projection[|*|, P1, Q1], Projection[|*|, P2, Q2]) =
      this match {
        case Fst(p1)      => (p1, Id())
        case Snd(p2)      => (Id(), p2)
        case Both(p1, p2) => (p1, p2)
      }
  }
  case class Fst[|*|[_, _], P, Q, B](p1: Proper[|*|, P, Q]) extends Par[|*|, P, B, Q, B] {
    override protected def discardFst[Q1, Q2](using ev: (Q |*| B) =:= (Q1 |*| Q2)): Proper[|*|, P |*| B, Q2] = ???

    override protected def discardSnd[Q1, Q2](using ev: (Q |*| B) =:= (Q1 |*| Q2)): Proper[|*|, P |*| B, Q1] = ???

    override protected def projectFst[Q1, Q2, R1](using ev: (Q |*| B) =:= (Q1 |*| Q2))(p1: Proper[|*|, Q1, R1]): Proper[|*|, P |*| B, R1 |*| Q2] = ???

    override protected def projectSnd[Q1, Q2, R2](using ev: (Q |*| B) =:= (Q1 |*| Q2))(p2: Proper[|*|, Q2, R2]): Proper[|*|, P |*| B, Q1 |*| R2] = ???
  }

  case class Snd[|*|[_, _], A, P, Q](p2: Proper[|*|, P, Q]) extends Par[|*|, A, P, A, Q] {
    override protected def discardFst[Q1, Q2](using ev: (A |*| Q) =:= (Q1 |*| Q2)): Proper[|*|, A |*| P, Q2] = ???

    override protected def discardSnd[Q1, Q2](using ev: (A |*| Q) =:= (Q1 |*| Q2)): Proper[|*|, A |*| P, Q1] = ???

    override protected def projectFst[Q1, Q2, R1](using ev: (A |*| Q) =:= (Q1 |*| Q2))(p1: Proper[|*|, Q1, R1]): Proper[|*|, A |*| P, R1 |*| Q2] = ???

    override protected def projectSnd[Q1, Q2, R2](using ev: (A |*| Q) =:= (Q1 |*| Q2))(p2: Proper[|*|, Q2, R2]): Proper[|*|, A |*| P, Q1 |*| R2] = ???
  }

  case class Both[|*|[_, _], P1, P2, Q1, Q2](p1: Proper[|*|, P1, Q1], p2: Proper[|*|, P2, Q2]) extends Par[|*|, P1, P2, Q1, Q2] {
    override protected def discardFst[q1, q2](using ev: (Q1 |*| Q2) =:= (q1 |*| q2)): Proper[|*|, P1 |*| P2, q2] = ???

    override protected def discardSnd[q1, q2](using ev: (Q1 |*| Q2) =:= (q1 |*| q2)): Proper[|*|, P1 |*| P2, q1] = ???

    override protected def projectFst[q1, q2, R1](using ev: (Q1 |*| Q2) =:= (q1 |*| q2))(p1: Proper[|*|, q1, R1]): Proper[|*|, P1 |*| P2, R1 |*| q2] = ???

    override protected def projectSnd[q1, q2, R2](using ev: (Q1 |*| Q2) =:= (q1 |*| q2))(p2: Proper[|*|, q2, R2]): Proper[|*|, P1 |*| P2, q1 |*| R2] = ???
  }

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
