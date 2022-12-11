package libretto.lambda

sealed trait Inj[|*|[_, _], A, B]

object Inj {
  case class Id[|*|[_, _], A]() extends Inj[|*|, A, A]
  case class Fst[|*|[_, _], X, A, B](i: Inj[|*|, X, A]) extends Inj[|*|, X, A |*| B]
  case class Snd[|*|[_, _], X, A, B](i: Inj[|*|, X, B]) extends Inj[|*|, X, A |*| B]

  def id[|*|[_, _], A]: Inj[|*|, A, A] =
    Id()

  def fst[|*|[_, _], X, A, B](i: Inj[|*|, X, A]): Inj[|*|, X, A |*| B] =
    Fst(i)

  def snd[|*|[_, _], X, A, B](i: Inj[|*|, X, B]): Inj[|*|, X, A |*| B] =
    Snd(i)
}
