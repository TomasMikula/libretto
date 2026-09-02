package libretto.lambda

/** A symmetric semigroupal category on a subset of Scala types.
  *
  * @tparam Obj  witnesses that a Scala type is an object of the category.
  * @tparam ->   morphism of the category
  * @tparam |*|  the monoidal product (tensor)
  */
trait NarrowSymmetricSemigroupalCategory[Obj[_], ->[_, _], |*|[_, _]]
  extends NarrowSemigroupalCategory[Obj, ->, |*|]
  with NarrowSymmetricWSemigroupalCategory[Obj, ->, [A, B, P] =>> (A |*| B) =:= P]
{
  def swap[A, B](wa: Obj[A], wb: Obj[B]): (A |*| B) -> (B |*| A)

  override def wswap[A, B, P, Q](
    wa: Obj[A], wb: Obj[B],
  )(
    p: (A |*| B) =:= P,
    q: (B |*| A) =:= Q,
  ): P -> Q = {
    val g: (A |*| B) -> (B |*| A) = swap(wa, wb)
    q.substituteCo[[X] =>> P -> X](p.substituteCo[[X] =>> X -> (B |*| A)](g))
  }

  def ix[A, B, C](wa: Obj[A], wb: Obj[B], wc: Obj[C]): ((A |*| B) |*| C) -> ((A |*| C) |*| B) =
    assocLR(wa, wb, wc) > par(id(wa), swap(wb, wc)) > assocRL(wa, wc, wb)

  def xi[A, B, C](wa: Obj[A], wb: Obj[B], wc: Obj[C]): (A |*| (B |*| C)) -> (B |*| (A |*| C)) =
    assocRL(wa, wb, wc) > par(swap(wa, wb), id(wc)) > assocLR(wb, wa, wc)

  def ixi[A, B, C, D](wa: Obj[A], wb: Obj[B], wc: Obj[C], wd: Obj[D]): ((A |*| B) |*| (C |*| D)) -> ((A |*| C) |*| (B |*| D)) =
    assocLR(wa, wb, tensor(wc, wd)) > par(id(wa), assocRL(wb, wc, wd) > par(swap(wb, wc), id(wd)) > assocLR(wc, wb, wd)) > assocRL(wa, wc, tensor(wb, wd))
}
