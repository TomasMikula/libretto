package libretto.lambda

/** A semigroupoid on a subset of Scala types, where composition demands
  * object-witnesses for the endpoint (and intermediate).
  *
  * @tparam Obj witnesses that a Scala type is an object of the category.
  * @tparam ->  morphism of the category
  */
trait NarrowSemigroupoid[Obj[_], ->[_, _]] {
  def narrowAndThen[A, B, C](
    f: A -> B,
    g: B -> C,
  )(using
    a: Obj[A],
    b: Obj[B],
    c: Obj[C],
  ): A -> C

  extension [A, B](f: A -> B) {
    def >-[C](g: B -> C)(using Obj[A], Obj[B], Obj[C]): A -> C =
      narrowAndThen(f, g)
  }
}
