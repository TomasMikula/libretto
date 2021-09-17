package libretto.impl

sealed trait Tupled[|*|[_, _], F[_], A] {
  def zip[B](that: Tupled[|*|, F, B]): Tupled[|*|, F, A |*| B] =
    Tupled.Zip(this, that)

  def mapReduce[G[_]](
    map: [x] => F[x] => G[x],
    zip: [x, y] => (G[x], G[y]) => G[x |*| y],
  ): G[A] =
    this match {
      case Tupled.Single(a) => map(a)
      case Tupled.Zip(x, y) => zip(x.mapReduce(map, zip), y.mapReduce(map, zip))
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
      case Tupled.Single(a) => Tupled.Single(f(a))
      case Tupled.Zip(x, y) => Tupled.Zip(x.trans(f), y.trans(f))
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
}