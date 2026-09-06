package libretto.lambda

/** A category on a subset of Scala types.
 *
 * @tparam Obj witnesses that a Scala type is an object of the category.
 * @tparam ->   morphism of the category
 */
trait NarrowCategory[Obj[_], ->[_, _]] extends Semigroupoid[->] {
  def id[A](using witness: Obj[A]): A -> A
}
