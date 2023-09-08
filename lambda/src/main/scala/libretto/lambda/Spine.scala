package libretto.lambda

/** Nested tuples with a hole.
 *
 * For example, a structure
 *
 * ```
 * (G[A], (G[B], (◯, G[C])))
 * ```
 *
 * where ◯ is the hole, can be represented as
 *
 * `Spine[**, G, F]` where `F[X] = A ** (B ** (X ** C))`
 *
 * Like [[Focus]], a `Spine` defines a path into a tupled structure,
 * but `Spine` also contains data along the path.
 *
 * @tparam ** the tuple type constructor
 * @tparam G tuple elements ("garnish" hanging from the spine)
 * @tparam F context of the hole
 */
sealed trait Spine[**[_, _], G[_], F[_]] {
  import Spine.*

  def focus: Focus[**, F] =
    this match
      case Id() => Focus.Id()

}

object Spine {
  case class Id[|*|[_, _], G[_]]() extends Spine[|*|, G, [x] =>> x]
}
