package libretto.lambda

import scala.collection.immutable.{:: as NonEmptyList}

/** An n-ary tuple of values `F[Ai]`,
 *  where `A = Nil ∙ A1 ∙ ... ∙ An`
 *  where `∙` associates to the left.
 *
 * Unlike [[Bin]], which is an arbitrarily nested binary tree,
 * the shape of nesting in [[TupleN]] is prescribed to be always associated to the left
 * and is conceptually used to represent flat n-ary tuples.
 */
sealed trait TupleN[∙[_, _], Nil, F[_], A] {
  def size: Int

  def nonEmpty[R](
    k: [A1, A2] => (A =:= (A1 ∙ A2)) ?=> R
  ): R

  def unravel[G[_, _]](
    f: [X] => F[X] => G[X, X],
  ): ParN[∙, Nil, G, A, A]

  def ∙[B](b: F[B]): TupleN[∙, Nil, F, A ∙ B] =
    TupleN.Snoc(this, b)

  def translate[G[_]](h: [a] => F[a] => G[a]): TupleN[∙, Nil, G, A]

  def foldL[G[_]](
    first: [a] => F[a] => G[Nil ∙ a],
    snoc: [a, b] => (G[a], F[b]) => G[a ∙ b],
  ): G[A]

  def toList[B](f: [a] => F[a] => B): NonEmptyList[B] =
    toList(f, scala.Nil)

  protected def toList[B](f: [a] => F[a] => B, acc: List[B]): NonEmptyList[B]
}

object TupleN {
  case class Single[∙[_, _], Nil, F[_], A](
    value: F[A],
  ) extends TupleN[∙, Nil, F, Nil ∙ A] {

    override def size: Int = 1

    override def nonEmpty[R](k: [A1, A2] => (Nil ∙ A =:= A1 ∙ A2) ?=> R): R =
      k[Nil, A]

    override def unravel[G[_, _]](
      f: [X] => F[X] => G[X, X],
    ): ParN[∙, Nil, G, Nil ∙ A, Nil ∙ A] =
      ParN.Single(f(value))

    override def translate[G[_]](h: [a] => F[a] => G[a]): TupleN[∙, Nil, G, Nil ∙ A] =
      Single(h(value))

    override def foldL[G[_]](
      first: [a] => F[a] => G[Nil ∙ a],
      snoc: [a, b] => (G[a], F[b]) => G[a ∙ b],
    ): G[Nil ∙ A] =
      first(value)

    override protected def toList[B](
      f: [a] => (F[a]) => B,
      acc: List[B],
    ): NonEmptyList[B] =
      NonEmptyList(f(value), acc)

  }

  case class Snoc[∙[_, _], Nil, F[_], Init, Last](
    init: TupleN[∙, Nil, F, Init],
    last: F[Last],
  ) extends TupleN[∙, Nil, F, Init ∙ Last] {

    override def size: Int = 1 + init.size

    override def nonEmpty[R](k: [A1, A2] => (Init ∙ Last =:= A1 ∙ A2) ?=> R): R =
      k[Init, Last]

    override def unravel[G[_, _]](
      f: [X] => F[X] => G[X, X],
    ): ParN[∙, Nil, G, Init ∙ Last, Init ∙ Last] =
      ParN.Snoc(init.unravel(f), f(last))

    override def translate[G[_]](h: [a] => F[a] => G[a]): TupleN[∙, Nil, G, Init ∙ Last] =
      Snoc(init.translate(h), h(last))

    override def foldL[G[_]](
      first: [a] => (F[a]) => G[Nil ∙ a],
      snoc: [a, b] => (G[a], F[b]) => G[a ∙ b],
    ): G[Init ∙ Last] =
      snoc(init.foldL(first, snoc), last)

    override protected def toList[B](
      f: [a] => (F[a]) => B,
      acc: List[B],
    ): NonEmptyList[B] =
      init.toList(f, f(last) :: acc)

  }
}
