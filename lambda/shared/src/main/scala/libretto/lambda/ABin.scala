package libretto.lambda

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
trait ABin[<*>[_, _], T[_], Rel[_, _, _], F[_], A, R] {

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
}
