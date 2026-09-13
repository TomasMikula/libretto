package libretto.lambda

import libretto.lambda.NarrowWSemigroupalCategory.×
import libretto.lambda.util.Exists
import libretto.lambda.util.Exists.Indeed

/** A semigroupal category on a subset of Scala types.
  *
  * @tparam Obj  witnesses that a Scala type is an object of the category.
  * @tparam ->   morphism of the category
  * @tparam |*|  the monoidal product (tensor)
  */
trait NarrowSemigroupalCategory[Obj[_], ->[_, _], |*|[_, _]]
  extends NarrowCategory[Obj, ->]
  with NarrowWSemigroupalCategory[Obj, ->, [A, B, P] =>> (A |*| B) =:= P]
{
  def narrowPar[A1, A2, B1, B2](
    f1: A1 -> B1,
    f2: A2 -> B2,
  )(using
    a1: Obj[A1], a2: Obj[A2],
    b1: Obj[B1], b2: Obj[B2],
  ): (A1 |*| A2) -> (B1 |*| B2)

  /** Combines the object-witnesses of two objects into an object-witness for their tensor (monoidal product). */
  def tensor[A, B](wa: Obj[A], wb: Obj[B]): Obj[A |*| B]

  /** [[tensor]] provided implicitly. */
  given [A, B] => (wa: Obj[A], wb: Obj[B]) => Obj[A |*| B] =
    tensor(wa, wb)

  def assocLR[A, B, C](using a: Obj[A], b: Obj[B], c: Obj[C]): ((A |*| B) |*| C) -> (A |*| (B |*| C))
  def assocRL[A, B, C](using a: Obj[A], b: Obj[B], c: Obj[C]): (A |*| (B |*| C)) -> ((A |*| B) |*| C)

  override def wtensor[A, B](
    wa: Obj[A],
    wb: Obj[B],
  ): Exists[[P] =>> (A |*| B) =:= P] =
    Exists(summon[(A |*| B) =:= (A |*| B)])

  override def tensorObj[A: Obj, B: Obj, P](p: (A |*| B) =:= P): Obj[P] =
    val ab: Obj[A |*| B] = tensor[A, B](summon, summon)
    p.substituteCo(ab)

  override def ipar[A1, A2, B1, B2](
    f1: A1 -×> B1,
    f2: A2 -×> B2,
  ): (A1 × A2) -×> (B1 × B2) =
    val underlying: (f1.Src |*| f2.Src) -> (f1.Tgt |*| f2.Tgt) =
      narrowPar(f1.underlying, f2.underlying)(using prdNObj(f1.src), prdNObj(f2.src), prdNObj(f1.tgt), prdNObj(f2.tgt))
    -×>(
      PrdN[f1.Src, f2.Src, f1.Src |*| f2.Src](summon)(f1.src, f2.src),
      PrdN[f1.Tgt, f2.Tgt, f1.Tgt |*| f2.Tgt](summon)(f1.tgt, f2.tgt),
    )(underlying)

  override def iassocLR[A, B, C](using a: PrdN.Intension[A], b: PrdN.Intension[B], c: PrdN.Intension[C]): ((A × B) × C) -×> (A × (B × C)) = {
    inline def go[P, Q, R](p: PrdN[A, P], q: PrdN[B, Q], r: PrdN[C, R]): ((A × B) × C) -×> (A × (B × C)) =
      val pq_r: PrdN[(A × B) × C, (P |*| Q) |*| R] = PrdN(summon)(PrdN(summon)(p, q), r)
      val p_qr: PrdN[A × (B × C), P |*| (Q |*| R)] = PrdN(summon)(p, PrdN(summon)(q, r))
      -×>(pq_r, p_qr)(assocLR(using prdNObj(p), prdNObj(q), prdNObj(r)))

    (PrdN.Intension.prdN(a), PrdN.Intension.prdN(b), PrdN.Intension.prdN(c)) match
      case (Indeed(p), Indeed(q), Indeed(r)) =>
        go(p, q, r)
  }

  override def iassocRL[A, B, C](using a: PrdN.Intension[A], b: PrdN.Intension[B], c: PrdN.Intension[C]): (A × (B × C)) -×> ((A × B) × C) = {
    inline def go[P, Q, R](p: PrdN[A, P], q: PrdN[B, Q], r: PrdN[C, R]): (A × (B × C)) -×> ((A × B) × C) =
      val p_qr: PrdN[A × (B × C), P |*| (Q |*| R)] = PrdN(summon)(p, PrdN(summon)(q, r))
      val pq_r: PrdN[(A × B) × C, (P |*| Q) |*| R] = PrdN(summon)(PrdN(summon)(p, q), r)
      -×>(p_qr, pq_r)(assocRL(using prdNObj(p), prdNObj(q), prdNObj(r)))

    (PrdN.Intension.prdN(a), PrdN.Intension.prdN(b), PrdN.Intension.prdN(c)) match
      case (Indeed(p), Indeed(q), Indeed(r)) =>
        go(p, q, r)
  }

  override def tensorUniq[A, B, P, Q](
    p: (A |*| B) =:= P,
    q: (A |*| B) =:= Q,
  ): P =:= Q =
    p.flip.andThen(q)

  def narrowFst[X, Y](f: X -> Y)[Z](using z: Obj[Z])(using x: Obj[X], y: Obj[Y]): (X |*| Z) -> (Y |*| Z) =
    narrowPar(f, id[Z])

  def narrowSnd[X](using x: Obj[X])[Y, Z](f: Y -> Z)(using y: Obj[Y], z: Obj[Z]): (X |*| Y) -> (X |*| Z) =
    narrowPar(id[X], f)
}
