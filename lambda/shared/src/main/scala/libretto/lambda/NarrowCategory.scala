package libretto.lambda

/** A category on a subset of Scala types.
 *
 * @tparam ->  morphism of the category
 * @tparam Obj witnesses that a Scala type is an object of the category.
 */
trait NarrowCategory[->[_, _], Obj[_]] extends Semigroupoid[->] {
  def id[A](witness: Obj[A]): A -> A
}
