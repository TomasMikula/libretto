package libretto.lambda

import libretto.lambda.util.Exists
import scala.collection.immutable.{:: as NonEmptyList}

/** Data types for working with non-empty heterogeneous lists of (unnamed) items of the form
 *
 *    Nil || A1 || ... || An
 *
 * where `||` is the separator of items (associates to the left).
 *
 * @see [[Items1Named]] for a list of *named* items.
 */
object Items1 {

  /**
    * Witnesses that `A` is one of `As`,
    * where `As` is of the form `Nil || A1 || A2 || ...`
    * (where `||` associates to the left).
    */
  sealed trait Member[||[_, _], Nil, A, As] {
    def inInit[B]: Member[||, Nil, A, As || B] =
      Member.InInit(this)

    def ownerTypeAsTuple[R](f: [X, Y] => (As =:= (X || Y)) ?=> R): R

    def ownerTypeIsTuple: Exists[[X] =>> Exists[[Y] =>> As =:= (X || Y)]] =
      ownerTypeAsTuple([X, Y] => (_) ?=> Exists(Exists(summon)))
  }

  object Member {
    case class Last[||[_, _], Nil, Init, Z]() extends Member[||, Nil, Z, Init || Z] {
      override def ownerTypeAsTuple[R](f: [X, Y] => ((Init || Z) =:= (X || Y)) ?=> R): R =
        f[Init, Z]
    }

    case class InInit[||[_, _], Nil, A, Init, Z](
      init: Member[||, Nil, A, Init],
    ) extends Member[||, Nil, A, Init || Z] {
      override def ownerTypeAsTuple[R](f: [X, Y] => ((Init || Z) =:= (X || Y)) ?=> R): R =
        f[Init, Z]
    }

    def single[||[_, _], Nil, A]: Member[||, Nil, A, Nil || A] =
      Last()
  }

  /** An n-ary tuple of values `F[Ai]`,
   *  where `A = Nil || A1 || ... || An`
   *  where `||` associates to the left.
   *
   * Unlike [[Bin]], which is an arbitrarily nested binary tree,
   * the shape of nesting in [[Items1.Product]] is prescribed to be always associated to the left
   * and is conceptually used to represent flat n-ary tuples.
   */
  sealed trait Product[||[_, _], Nil, F[_], A] {
    def size: Int

    def nonEmpty[R](
      k: [A1, A2] => (A =:= (A1 || A2)) ?=> R
    ): R

    def unravel[G[_, _]](
      f: [X] => F[X] => G[X, X],
    ): ParN[||, Nil, G, A, A]

    def ||[B](b: F[B]): Product[||, Nil, F, A || B] =
      Product.Snoc(this, b)

    def translate[G[_]](h: [a] => F[a] => G[a]): Product[||, Nil, G, A]

    def foldL[G[_]](
      first: [a] => F[a] => G[Nil || a],
      snoc: [a, b] => (G[a], F[b]) => G[a || b],
    ): G[A]

    def toList[B](f: [a] => F[a] => B): NonEmptyList[B] =
      toList(f, scala.Nil)

    protected def toList[B](f: [a] => F[a] => B, acc: List[B]): NonEmptyList[B]
  }

  object Product {
    case class Single[||[_, _], Nil, F[_], A](
      value: F[A],
    ) extends Product[||, Nil, F, Nil || A] {

      override def size: Int = 1

      override def nonEmpty[R](k: [A1, A2] => ((Nil || A) =:= (A1 || A2)) ?=> R): R =
        k[Nil, A]

      override def unravel[G[_, _]](
        f: [X] => F[X] => G[X, X],
      ): ParN[||, Nil, G, Nil || A, Nil || A] =
        ParN.Single(f(value))

      override def translate[G[_]](h: [a] => F[a] => G[a]): Product[||, Nil, G, Nil || A] =
        Single(h(value))

      override def foldL[G[_]](
        first: [a] => F[a] => G[Nil || a],
        snoc: [a, b] => (G[a], F[b]) => G[a || b],
      ): G[Nil || A] =
        first(value)

      override protected def toList[B](
        f: [a] => (F[a]) => B,
        acc: List[B],
      ): NonEmptyList[B] =
        NonEmptyList(f(value), acc)

    }

    case class Snoc[||[_, _], Nil, F[_], Init, Last](
      init: Product[||, Nil, F, Init],
      last: F[Last],
    ) extends Product[||, Nil, F, Init || Last] {

      override def size: Int = 1 + init.size

      override def nonEmpty[R](k: [A1, A2] => ((Init || Last) =:= (A1 || A2)) ?=> R): R =
        k[Init, Last]

      override def unravel[G[_, _]](
        f: [X] => F[X] => G[X, X],
      ): ParN[||, Nil, G, Init || Last, Init || Last] =
        ParN.Snoc(init.unravel(f), f(last))

      override def translate[G[_]](h: [a] => F[a] => G[a]): Product[||, Nil, G, Init || Last] =
        Snoc(init.translate(h), h(last))

      override def foldL[G[_]](
        first: [a] => (F[a]) => G[Nil || a],
        snoc: [a, b] => (G[a], F[b]) => G[a || b],
      ): G[Init || Last] =
        snoc(init.foldL(first, snoc), last)

      override protected def toList[B](
        f: [a] => (F[a]) => B,
        acc: List[B],
      ): NonEmptyList[B] =
        init.toList(f, f(last) :: acc)

    }
  }
}
