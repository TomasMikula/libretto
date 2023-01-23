package libretto.lambda

import libretto.util.{BiInjective, Injective, Masked, TypeEq}
import libretto.util.TypeEq.Refl

/**
 * Binary tree with leafs holding values of types `F[X]`, `F[Y]`, ...
 * The complete structure of the tree is expressed by the type `A`, using the tags for branches and leafs.
 *
 * @tparam <*> tag for branches
 * @tparam T tag for leafs.
 * @tparam F value type of leafs. Each leaf holds a value of type `F[T]`, for some type `T`.
 * @tparam A captures the complete structure of the tree
 */
sealed trait Bin[<*>[_, _], T[_], F[_], A] {
  import Bin._

  def <*>[B](that: Bin[<*>, T, F, B]): Bin[<*>, T, F, A <*> B] =
    Branch(this, that)

  def mask: Masked[Bin[<*>, T, F, *], A] =
    Masked(this)

  def getValue[V](using
    leafIsNotBranch: [x, y, z] => (T[x] =:= (y <*> z)) => Nothing,
    T: Injective[T],
    ev: A =:= T[V],
  ): F[V] =
    ev match { case TypeEq(Refl()) => Bin.valueOf(this) }
}

object Bin {
  case class Branch[<*>[_, _], T[_], F[_], A, B](l: Bin[<*>, T, F, A], r: Bin[<*>, T, F, B]) extends Bin[<*>, T, F, A <*> B]
  case class Leaf[<*>[_, _], T[_], F[_], A](value: F[A]) extends Bin[<*>, T, F, T[A]]

  def branchesOf[<*>[_, _], T[_], F[_], A, B](tree: Bin[<*>, T, F, A <*> B])(using
    leafIsNotBranch: [x, y, z] => (T[x] =:= (y <*> z)) => Nothing,
  )(using
    BiInjective[<*>],
  ): (Bin[<*>, T, F, A], Bin[<*>, T, F, B]) =
    tree.mask.visit[(Bin[<*>, T, F, A], Bin[<*>, T, F, B])](
      [X] => (tree: Bin[<*>, T, F, X], ev: X =:= (A <*> B)) =>
        tree match {
          case t: Branch[br, lf, f, a, b] =>
            (summon[(a <*> b) =:= X] andThen ev) match
              case BiInjective[<*>](TypeEq(Refl()), TypeEq(Refl())) =>
                (t.l, t.r)
          case _: Leaf[br, lf, f, v] =>
            leafIsNotBranch[v, A, B](ev)
        }
    )

  def valueOf[<*>[_, _], T[_], F[_], A](tree: Bin[<*>, T, F, T[A]])(using
    leafIsNotBranch: [x, y, z] => (T[x] =:= (y <*> z)) => Nothing,
  )(using
    Injective[T],
  ): F[A] =
    tree.mask.visit[F[A]](
      [X] => (tree: Bin[<*>, T, F, X], ev: X =:= T[A]) =>
        tree match
          case l: Leaf[br, t, f, x] =>
            (summon[T[x] =:= X] andThen ev) match
              case Injective[T](TypeEq(Refl())) =>
                l.value
          case _: Branch[br, t, f, a, b] => leafIsNotBranch[A, a, b](ev.flip)
    )

  given [<*>[_, _], T[_], F[_]](using
    leafIsNotBranch: [x, y, z] => (T[x] =:= (y <*> z)) => Nothing,
  )(using
    BiInjective[<*>],
  ): Cartesian[<*>, Bin[<*>, T, F, *]] with {
    override def zip[A, B](a: Bin[<*>, T, F, A], b: Bin[<*>, T, F, B]): Bin[<*>, T, F, A <*> B] =
      Branch(a, b)

    override def unzip[A, B](ab: Bin[<*>, T, F, A <*> B]): (Bin[<*>, T, F, A], Bin[<*>, T, F, B]) =
      branchesOf(ab)
  }
}
