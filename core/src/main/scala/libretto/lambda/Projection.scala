package libretto.lambda

sealed trait Projection[|*|[_, _], P, Q] {
  def at[F[_]](f: Focus[|*|, F]): Projection[|*|, F[P], F[Q]]
}

object Projection {
  case class Id[|*|[_, _], P]() extends Projection[|*|, P, P] {
    override def at[F[_]](f: Focus[|*|, F]): Projection[|*|, F[P], F[P]] = Id()
  }

  sealed trait Proper[|*|[_, _], P, Q] extends Projection[|*|, P, Q] {
    override def at[F[_]](f: Focus[|*|, F]): Projection.Proper[|*|, F[P], F[Q]] =
      f match {
        case Focus.Id()    => this
        case Focus.Fst(f1) => Fst(this.at(f1))
        case Focus.Snd(f2) => Snd(this.at(f2))
      }
  }
  case class DiscardFst[|*|[_, _], A, B]() extends Proper[|*|, A |*| B, B]
  case class DiscardSnd[|*|[_, _], A, B]() extends Proper[|*|, A |*| B, A]
  case class Fst[|*|[_, _], P, Q, B](p1: Proper[|*|, P, Q]) extends Proper[|*|, P |*| B, Q |*| B]
  case class Snd[|*|[_, _], A, P, Q](p2: Proper[|*|, P, Q]) extends Proper[|*|, A |*| P, A |*| Q]
  case class Par[|*|[_, _], P1, P2, Q1, Q2](p1: Proper[|*|, P1, Q1], p2: Proper[|*|, P2, Q2]) extends Proper[|*|, P1 |*| P2, Q1 |*| Q2]

  def id[|*|[_, _], P]: Projection[|*|, P, P] = Id()
  def discardFst[|*|[_, _], A, B]: Proper[|*|, A |*| B, B] = DiscardFst()
  def discardSnd[|*|[_, _], A, B]: Proper[|*|, A |*| B, A] = DiscardSnd()
  def fst[|*|[_, _], P, Q, B](p1: Proper[|*|, P, Q]): Proper[|*|, P |*| B, Q |*| B] = Fst(p1)
  def snd[|*|[_, _], A, P, Q](p2: Proper[|*|, P, Q]): Proper[|*|, A |*| P, A |*| Q] = Snd(p2)
  def par[|*|[_, _], P1, P2, Q1, Q2](p1: Proper[|*|, P1, Q1], p2: Proper[|*|, P2, Q2]): Proper[|*|, P1 |*| P2, Q1 |*| Q2] = Par(p1, p2)
}
