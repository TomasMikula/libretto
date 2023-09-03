package libretto.lambda

import libretto.lambda.util.{Exists, UniqueTypeArg}
import scala.annotation.targetName

opaque type Tupled[|*|[_, _], F[_], A] =
  Bin[|*|, [x] =>> x, F, A]

object Tupled {
  def atom[|*|[_, _], F[_], A](v: F[A]): Tupled[|*|, F, A] =
    Bin.Leaf(v)

  def zip[|*|[_, _], F[_], X, Y](
    _1: Tupled[|*|, F, X],
    _2: Tupled[|*|, F, Y],
  ): Tupled[|*|, F, X |*| Y] =
    Bin.Branch(_1, _2)

  def fromBin[|*|[_, _], F[_], A](value: Bin[|*|, [x] =>> x, F, A]): Tupled[|*|, F, A] =
    value

  extension [|*|[_, _], F[_], A](a: Tupled[|*|, F, A]) {
    def trans[G[_]](f: [x] => F[x] => G[x]): Tupled[|*|, G, A] =
      a.mapLeafs(f)

    @targetName("zip_infix")
    def zip[B](b: Tupled[|*|, F, B]): Tupled[|*|, F, A |*| B] =
      Tupled.zip(a, b)

    def asBin: Bin[|*|, [x] =>> x, F, A] =
      a

    def foldMap[G[_]](
      map: [x] => F[x] => G[x],
      zip: [x, y] => (G[x], G[y]) => G[x |*| y],
    ): G[A] =
      a.foldMap[G](map, zip)

    def foldMap0[B](
      map: [x] => F[x] => B,
      reduce: (B, B) => B,
    ): B =
      a.foldMap0[B](map, reduce)

    def fold(zip: [x, y] => (F[x], F[y]) => F[x |*| y]): F[A] =
      foldMap[F]([x] => (fx: F[x]) => fx, zip)

    def deduplicateLeafs[->[_, _]](
      dup: [x] => F[x] => x -> (x |*| x),
    )(using
      F: UniqueTypeArg[F],
      shuffled: Shuffled[->, |*|],
    ): Exists[[X] =>> (Tupled[|*|, F, X], shuffled.Shuffled[X, A])] =
      a.deduplicateLeafs(dup)

    def product[B, ->[_, _]](b: Tupled[|*|, F, B])(
      discardFst: [X, Y] => F[X] => (X |*| Y) -> Y,
    )(using
      F: UniqueTypeArg[F],
      shuffled: Shuffled[->, |*|],
    ): Exists[[P] =>> (
      Tupled[|*|, F, P],
      shuffled.Shuffled[P, A],
      shuffled.Shuffled[P, B],
    )] =
      (a product b)(discardFst)
  }

  given [|*|[_, _], F[_]]: Zippable[|*|, Tupled[|*|, F, _]] with {
    override def zip[A, B](fa: Tupled[|*|, F, A], fb: Tupled[|*|, F, B]): Tupled[|*|, F, A |*| B] =
      Tupled.zip(fa, fb)
  }
}