package libretto.lambda

import libretto.lambda.NarrowWSemigroupalCategory.×
import libretto.lambda.util.Exists.Indeed

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

  override def iswap[A, B](using a: PrdN.Intension[A], b: PrdN.Intension[B]): (A × B) -×> (B × A) = {
    inline def go[P, Q](p: PrdN[A, P], q: PrdN[B, Q]): (A × B) -×> (B × A) =
      val pq: PrdN[A × B, P |*| Q] = PrdN[P, Q, P |*| Q](summon)(p, q)
      val qp: PrdN[B × A, Q |*| P] = PrdN[Q, P, Q |*| P](summon)(q, p)
      -×>(pq, qp)(swap[P, Q](using prdNObj(p), prdNObj(q)))

    (PrdN.Intension.prdN(a), PrdN.Intension.prdN(b)) match
      case (Indeed(p), Indeed(q)) =>
        go(p, q)
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
