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
      case Id()        => Focus.Id()
      case Fst(fst, _) => Focus.Fst(fst.focus)
      case Snd(_, snd) => Focus.Snd(snd.focus)

  def plugFold[A](a: G[A])(using Zippable[**, G]): G[F[A]] =
    this match
      case Id() => a
      case Fst(fst, snd) => fst.plugFold(a) zip snd
      case Snd(fst, snd) => fst zip snd.plugFold(a)

  def inFst[B](b: G[B]): Spine[**, G, [x] =>> F[x] ** B] =
    Fst(this, b)

  def inSnd[A](a: G[A]): Spine[**, G, [x] =>> A ** F[x]] =
    Snd(a, this)
}

object Spine {
  case class Id[|*|[_, _], G[_]]() extends Spine[|*|, G, [x] =>> x]
  case class Fst[|*|[_, _], G[_], F[_], B](
    fst: Spine[|*|, G, F],
    snd: G[B],
  ) extends Spine[|*|, G, [x] =>> F[x] |*| B]
  case class Snd[|*|[_, _], G[_], F[_], A](
    fst: G[A],
    snd: Spine[|*|, G, F],
  ) extends Spine[|*|, G, [x] =>> A |*| F[x]]
}
