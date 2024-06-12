package libretto.lambda

import libretto.lambda.util.{Exists, UniqueTypeArg}
import scala.annotation.targetName
import libretto.lambda.Bin.{Branch, Leaf}

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
    infix def zip[B](b: Tupled[|*|, F, B]): Tupled[|*|, F, A |*| B] =
      Tupled.zip(a, b)

    def asBin: Bin[|*|, [x] =>> x, F, A] =
      a

    def foldMapWith[G[_]](
      map: [x] => F[x] => G[x],
      zip: [x, y] => (G[x], G[y]) => G[x |*| y],
    ): G[A] =
      a.foldMapWith[G](map, zip)

    def foldMap[G[_]](
      map: [x] => F[x] => G[x],
    )(using
      G: Zippable[|*|, G],
    ): G[A] =
      a.foldMap[G](map)

    def foldMap0[B](
      map: [x] => F[x] => B,
      reduce: (B, B) => B,
    ): B =
      a.foldMap0[B](map, reduce)

    def foldWith(zip: [x, y] => (F[x], F[y]) => F[x |*| y]): F[A] =
      foldMapWith[F]([x] => (fx: F[x]) => fx, zip)

    def fold(using F: Zippable[|*|, F]): F[A] =
      foldWith([x, y] => (fx: F[x], fy: F[y]) => F.zip(fx, fy))

    def foldRight[B](b: B)(f: [x] => (F[x], B) => B): B =
      a.foldRight[B](b)(f)

    def toList[B](f: [T] => F[T] => B): List[B] =
      foldRight[List[B]](Nil)([x] => (fx: F[x], acc: List[B]) => f(fx) :: acc)

    def deduplicateLeafs[->[_, _]](
      dup: [x] => F[x] => x -> (x |*| x),
    )(using
      F: UniqueTypeArg[F],
      shuffled: Shuffled[->, |*|],
    ): Exists[[X] =>> (Tupled[|*|, F, X], shuffled.Shuffled[X, A])] =
      a.deduplicateLeafs(dup)

    infix def union[B, ->[_, _]](b: Tupled[|*|, F, B])(
      discardFst: [X, Y] => F[X] => (X |*| Y) -> Y,
    )(using
      F: UniqueTypeArg[F],
      shuffled: Shuffled[->, |*|],
    ): Exists[[P] =>> (
      Tupled[|*|, F, P],
      shuffled.Shuffled[P, A],
      shuffled.Shuffled[P, B],
    )] =
      (a union b)(discardFst)
  }

  def unzip[|*|[_, _], F[_], A, B](
    ab: Tupled[|*|, F, A |*| B],
  )(using F: Unzippable[|*|, F]): (Tupled[|*|, F, A], Tupled[|*|, F, B]) =
    ab match
      case Bin.Branch(l, r) =>
        (l, r)
      case Bin.Leaf(fab) =>
        val (fa, fb) = F.unzip(fab)
        (atom(fa), atom(fb))

  given [|*|[_, _], F[_]]: Zippable[|*|, Tupled[|*|, F, _]] with {
    override def zip[A, B](fa: Tupled[|*|, F, A], fb: Tupled[|*|, F, B]): Tupled[|*|, F, A |*| B] =
      Tupled.zip(fa, fb)
  }

  object Atom {
    def unapply[|*|[_, _], F[_], A](a: Tupled[|*|, F, A]): Option[F[A]] =
      a match
        case Leaf(a)      => Some(a)
        case Branch(_, _) => None

  }

  object <*> {
    def unapply[|*|[_, _], F[_], A, B](
      ab: Tupled[|*|, F, A |*| B],
    )(using F: Unzippable[|*|, F]): (Tupled[|*|, F, A], Tupled[|*|, F, B]) =
      unzip(ab)
  }
}