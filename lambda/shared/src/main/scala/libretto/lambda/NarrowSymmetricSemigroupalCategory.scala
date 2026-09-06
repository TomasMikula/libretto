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
  def swap[A, B](using wa: Obj[A], wb: Obj[B]): (A |*| B) -> (B |*| A)

  override def wswap[A, B](
    wa: Obj[A],
    wb: Obj[B],
  )[P, Q](
    p: (A |*| B) =:= P,
    q: (B |*| A) =:= Q,
  ): P -> Q = {
    val g: (A |*| B) -> (B |*| A) = swap(using wa, wb)
    q.substituteCo[[X] =>> P -> X](p.substituteCo[[X] =>> X -> (B |*| A)](g))
  }

  def ix[A, B, C](using Obj[A], Obj[B], Obj[C]): ((A |*| B) |*| C) -> ((A |*| C) |*| B) =
    assocLR[A, B, C] > narrowPar(id[A], swap[B, C]) > assocRL[A, C, B]

  def xi[A, B, C](using Obj[A], Obj[B], Obj[C]): (A |*| (B |*| C)) -> (B |*| (A |*| C)) =
    assocRL[A, B, C] > narrowPar(swap[A, B], id[C]) > assocLR[B, A, C]

  def ixi[A, B, C, D](using Obj[A], Obj[B], Obj[C], Obj[D]): ((A |*| B) |*| (C |*| D)) -> ((A |*| C) |*| (B |*| D)) =
    assocLR[A, B, C |*| D] >
      narrowPar(id[A], assocRL[B, C, D] > narrowPar(swap[B, C], id[D]) > assocLR[C, B, D]) >
      assocRL[A, C, B |*| D]
}
