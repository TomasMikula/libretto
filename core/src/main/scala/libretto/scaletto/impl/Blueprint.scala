package libretto.scaletto.impl

import phantoms.*

/** A representation of Libretto functions. Unlike [[-⚬]], it is a proper blueprint
 * in that it does not exploit cycles in the (Scala-level) object graph.
 */
enum Blueprint[A, B]:
  case Regular(value: Fun[Blueprint, A, B])

  case FunRef(
    id: Object, // XXX: use a proper Id type
    f: Blueprint[A, B],
  )

  case ConstSub[A, B](
    f: Blueprint[A, B],
  ) extends Blueprint[One, Sub[A, B]]

  private[impl] lazy val sizeAndRefs: SizeAndRefs =
    import SizeAndRefs.one

    this match
      case FunRef(id, f) =>
        SizeAndRefs(1, Map(id -> f))
      case ConstSub(f) =>
        one + f.sizeAndRefs
      case Regular(f) =>
        one + f.foldMonoid([X, Y] => (g: Blueprint[X, Y]) => g.sizeAndRefs)

private[impl] case class SizeAndRefs(size: Long, refs: Map[Object, Blueprint[?, ?]]):
  def +(that: SizeAndRefs): SizeAndRefs =
    SizeAndRefs(this.size + that.size, this.refs ++ that.refs)

  def +(n: Int): SizeAndRefs =
    SizeAndRefs(size + n, refs)

private[impl] object SizeAndRefs {
  def apply(n: Int): SizeAndRefs =
    SizeAndRefs(n, Map.empty)

  val one: SizeAndRefs =
    SizeAndRefs(1)

  given Monoid[SizeAndRefs] with
    override def unit: SizeAndRefs = SizeAndRefs(0, Map.empty)
    override def combine(l: SizeAndRefs, r: SizeAndRefs): SizeAndRefs = l + r
}
