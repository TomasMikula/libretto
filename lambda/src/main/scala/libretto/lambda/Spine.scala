package libretto.lambda

import libretto.lambda.util.SourcePos

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

  def knitFoldMap[H[_]](
    k: Knit[**, F],
    f: [x] => G[x] => H[x],
  )(using Zippable[**, H]): H[k.Res]

  def knit(k: Knit[**, F]): Tupled[**, G, k.Res] =
    knitFoldMap[Tupled[**, G, _]](k, [x] => (gx: G[x]) => Tupled.atom(gx))

  def knitFold(k: Knit[**, F])(using Zippable[**, G]): G[k.Res] =
    knitFoldMap[G](k, [x] => (gx: G[x]) => gx)

  def inFst[B](b: G[B]): Spine[**, G, [x] =>> F[x] ** B] =
    Fst(this, b)

  def inSnd[A](a: G[A]): Spine[**, G, [x] =>> A ** F[x]] =
    Snd(a, this)
}

object Spine {
  case class Id[|*|[_, _], G[_]]() extends Spine[|*|, G, [x] =>> x] {
    override def knitFoldMap[H[_]](
      k: Knit[|*|, [x] =>> x],
      f: [x] => G[x] => H[x],
    )(using Zippable[|*|, H]): H[k.Res] =
      type Fresh
      val ev = k.proveProduct[Fresh]
      type A = ev.T
      type B = ev.value.T
      val impossible: Fresh =:= (A |*| B) = ev.value.value
      throw AssertionError("Impossible for a fresh type to be equal to A |*| B")
  }

  case class Fst[|*|[_, _], G[_], F[_], B](
    fst: Spine[|*|, G, F],
    snd: G[B],
  ) extends Spine[|*|, G, [x] =>> F[x] |*| B] {
    override def knitFoldMap[H[_]](
      k: Knit[|*|, [x] =>> F[x] |*| B],
      f: [x] => G[x] => H[x],
    )(using Zippable[|*|, H]): H[k.Res] =
      throw NotImplementedError(s"at ${summon[SourcePos]}")
  }

  case class Snd[|*|[_, _], G[_], F[_], A](
    fst: G[A],
    snd: Spine[|*|, G, F],
  ) extends Spine[|*|, G, [x] =>> A |*| F[x]] {
    override def knitFoldMap[H[_]](
      k: Knit[|*|, [x] =>> A |*| F[x]],
      f: [x] => G[x] => H[x],
    )(using Zippable[|*|, H]): H[k.Res] =
      throw NotImplementedError(s"at ${summon[SourcePos]}")
  }
}
