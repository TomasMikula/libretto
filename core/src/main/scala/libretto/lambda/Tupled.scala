package libretto.lambda

import libretto.util.Zippable

sealed trait Tupled[|*|[_, _], F[_], A] {
  import Tupled._

  def zip[B](that: Tupled[|*|, F, B]): Tupled[|*|, F, A |*| B] =
    Zip(this, that)

  def mapReduce[G[_]](
    map: [x] => F[x] => G[x],
    zip: [x, y] => (G[x], G[y]) => G[x |*| y],
  ): G[A] =
    this match {
      case Single(a) => map(a)
      case Zip(x, y) => zip(x.mapReduce(map, zip), y.mapReduce(map, zip))
    }

  def mapReduce0[B](
    map: [x] => F[x] => B,
    reduce: (B, B) => B,
  ): B = {
    type G[x] = B
    mapReduce[G](map, [x, y] => (x: G[x], y: G[y]) => reduce(x, y))
  }

  def fold(zip: [x, y] => (F[x], F[y]) => F[x |*| y]): F[A] =
    mapReduce[F]([x] => (fx: F[x]) => fx, zip)

  def trans[G[_]](f: [x] => F[x] => G[x]): Tupled[|*|, G, A] =
    this match {
      case Single(a) => Single(f(a))
      case Zip(x, y) => Zip(x.trans(f), y.trans(f))
    }

  def isEqualTo(that: Tupled[|*|, F, A])(equal: [X] => (F[X], F[X]) => Boolean): Boolean =
    (this, that) match {
      case (Single(fa) , Single(fb)) =>
        equal(fa, fb)
      case (Zip(a1, a2), Zip(b1, b2)) =>
        (a1 isEqualTo b1)(equal) && (a2 isEqualTo b2)(equal)
      case _ =>
        false
    }
}

object Tupled {
  case class Single[|*|[_, _], F[_], A](v: F[A]) extends Tupled[|*|, F, A]
  case class Zip[|*|[_, _], F[_], X, Y](_1: Tupled[|*|, F, X], _2: Tupled[|*|, F, Y]) extends Tupled[|*|, F, X |*| Y]

  def unzip[|*|[_, _], F[_], A, B](ab: Tupled[|*|, F, A |*| B]): Option[(Tupled[|*|, F, A], Tupled[|*|, F, B])] =
    ab match {
      case Zip(a, b) => Some((a, b))
      case Single(_) => None
    }

  given [|*|[_, _], F[_]]: Zippable[|*|, Tupled[|*|, F, *]] with {
    override def zip[A, B](fa: Tupled[|*|, F, A], fb: Tupled[|*|, F, B]): Tupled[|*|, F, A |*| B] =
      Zip(fa, fb)
  }
}