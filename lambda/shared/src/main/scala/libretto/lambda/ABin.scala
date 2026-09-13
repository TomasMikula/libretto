package libretto.lambda

import libretto.lambda.util.{BiInjective, Functional2, Injective, Masked, TypeEq}
import libretto.lambda.util.TypeEq.Refl

/**
 * Type-aligned variant of [[Bin]] (a binary tree), where each node has an associated type
 * and parent node type relates to its chilrd nodes' types through `Rel`.
 *
 * Example: The tree
 *
 * ```
 *       R
 *     /   \
 *   P       Q
 *  / \     / \
 * A   B   C   D
 * ```
 *
 * when represented as `ABin[<*>, T, Rel, F, (T[A] <*> T[B]) <*> (T[C] <*> T[D]), R]`
 * (with inner node types `P` and `Q` being existential), holds the following data:
 *
 * - leaves: `F[A]`, `F[B]`, `F[C]`, `F[D]`
 * - branches: `Rel[A, B, P]`, `Rel[C, D, Q]`, `Rel[P, Q, R]`
 *
 * @tparam <*> tag for branches, as it appears in `A`
 * @tparam T tag for leafs, as it appears in `A`
 * @tparam Rel value type of branches, relating child node types to the parent node type.
 *   `Rel[A, B, P]` is stored in a branch node whose type is `P` and whose child nodes' types are `A` and `B`, respectively.
 * @tparam F value type of leaves. Each leaf holds a value of type `F[X]`, for some type `X`
 *   (but appears in `A` as `T[X]`).
 * @tparam A captures the shape of the tree via grouping the leaf types.
 *   Example: `(T[V] <*> T[W]) <*> (T[X] <*> (T[Y] <*> T[Z]))`
 * @tparam R the type associated with the root of the tree.
 */
sealed trait ABin[<*>[_, _], T[_], Rel[_, _, _], F[_], A, R] {
  def maskShape: Masked[ABin[<*>, T, Rel, F, _, R], A] =
    Masked(this)
}

object ABin {
  case class Leaf[<*>[_, _], T[_], Rel[_, _, _], F[_], A](
    value: F[A],
  ) extends ABin[<*>, T, Rel, F, T[A], A]

  case class Branch[<*>[_, _], T[_], Rel[_, _, _], F[_], A, B, P, Q, R](
    l: ABin[<*>, T, Rel, F, A, P],
    r: ABin[<*>, T, Rel, F, B, Q],
    value: Rel[P, Q, R],
  ) extends ABin[<*>, T, Rel, F, A <*> B, R]

  /** Given two trees of the same shape `A`, proves that their root types are equal. */
  def uniq[<*>[_, _], T[_], Rel[_, _, _], F[_], A, R, S](
    a: ABin[<*>, T, Rel, F, A, R],
    b: ABin[<*>, T, Rel, F, A, S],
  )(using
    leafIsNotBranch: [x, y, z] => (T[x] =:= (y <*> z)) => Nothing,
    P: BiInjective[<*>],
    T: Injective[T],
    rel: Functional2[Rel],
  ): R =:= S =
    a match
      case la: Leaf[br, lf, rl, f, x] =>
        val evA = summon[T[x] =:= A]
        b.maskShape.visit[R =:= S](
          [X] => (b0: ABin[<*>, T, Rel, F, X, S], evX: X =:= A) =>
            b0 match
              case lb: Leaf[br2, lf2, rl2, f2, x2] =>
                val evB = summon[T[x2] =:= X]
                (evA andThen evX.flip andThen evB.flip) match
                  case Injective[T](TypeEq(Refl())) =>
                    summon[R =:= S]
              case bb: Branch[br2, lf2, rl2, f2, a2, b2, p2, q2, s2] =>
                val evB = summon[(a2 <*> b2) =:= X]
                leafIsNotBranch[x, a2, b2](evA andThen evX.flip andThen evB.flip)
        )
      case ba: Branch[br, lf, rl, f, a1, b1, p1, q1, r1] =>
        val evA = summon[(a1 <*> b1) =:= A]
        b.maskShape.visit[R =:= S](
          [X] => (b0: ABin[<*>, T, Rel, F, X, S], evX: X =:= A) =>
            b0 match
              case lb: Leaf[br2, lf2, rl2, f2, x2] =>
                val evB = summon[T[x2] =:= X]
                leafIsNotBranch[x2, a1, b1]((evA andThen evX.flip andThen evB.flip).flip)
              case bb: Branch[br2, lf2, rl2, f2, a2, b2, p2, q2, s2] =>
                val evB = summon[(a2 <*> b2) =:= X]
                (evA andThen evX.flip andThen evB.flip) match
                  case BiInjective[<*>](TypeEq(Refl()), TypeEq(Refl())) =>
                    val evP = uniq(ba.l, bb.l)
                    val evQ = uniq(ba.r, bb.r)
                    val rl1: Rel[p1, q1, r1] = ba.value
                    val rl2: Rel[p2, q2, s2] = bb.value
                    val rl2a = evP.flip.substituteCo[[C] =>> Rel[C, q2, s2]](rl2)
                    val rl2b = evQ.flip.substituteCo[[C] =>> Rel[p1, C, s2]](rl2a)
                    rl1 uniq rl2b
        )
}
