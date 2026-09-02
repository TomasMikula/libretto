package libretto.lambda

/** A symmetric semigroupal category on a subset of Scala types (narrow), where the monoidal product (tensor]
  * is witnessed (hence "W" in WSemigroupal) by a ternary relation `Prd[A, B, P]` that `P` is the tensor of `A` and `B`.
  *
  * @tparam Obj  witnesses that a Scala type is an object of the category.
  * @tparam ->   morphism of the category
  * @tparam Prd  witnesses tensor formation: `Prd[A, B, P]` means that `P` is the tensor of `A` and `B`.
  */
trait NarrowSymmetricWSemigroupalCategory[Obj[_], ->[_, _], Prd[_, _, _]]
  extends NarrowWSemigroupalCategory[Obj, ->, Prd]
{
  def wswap[A, B, P, Q](wa: Obj[A], wb: Obj[B])(
    p: Prd[A, B, P],
    q: Prd[B, A, Q],
  ): P -> Q
}
