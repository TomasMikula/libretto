package libretto.lambda

/** A semigroupal category on a subset of Scala types (narrow), where the monoidal product (tensor)
  * is not given as a fixed binary type constructor, but is *witnessed* (hence "W" in WSemigroupal)
  * by a ternary relation `Prd[A, B, P]` that `P` is the tensor of `A` and `B`.
  *
  * @tparam Obj  witnesses that a Scala type is an object of the category.
  * @tparam ->   morphism of the category
  * @tparam Prd  witnesses tensor formation: `Prd[A, B, P]` means that `P` is the tensor of `A` and `B`.
  */
trait NarrowWSemigroupalCategory[Obj[_], ->[_, _], Prd[_, _, _]]
  extends NarrowCategory[Obj, ->]
{
  /** Witness that `P` is the monoidal tensor (product) of `A` and `B`,
    * and combine the object-witnesses of `A` and `B` into an object-witness for `P`.
    */
  def wtensor[A, B, P](wa: Obj[A], wb: Obj[B])(
    p: Prd[A, B, P],
  ): Obj[P]

  def wpar[A1, A2, B1, B2](
    f1: A1 -> B1,
    f2: A2 -> B2,
  )(using
    a1: Obj[A1], a2: Obj[A2],
    b1: Obj[B1], b2: Obj[B2],
  )[P, Q](
    pSrc: Prd[A1, A2, P],
    pTgt: Prd[B1, B2, Q],
  ): P -> Q

  def wassocLR[A, B, C](
    a: Obj[A], b: Obj[B], c: Obj[C],
  )[AB, AB_C, BC, A_BC](
    pAB: Prd[A, B, AB],
    pAB_C: Prd[AB, C, AB_C],
    pBC: Prd[B, C, BC],
    pA_BC: Prd[A, BC, A_BC],
  ): AB_C -> A_BC

  def wassocRL[A, B, C](
    a: Obj[A], b: Obj[B], c: Obj[C],
  )[BC, A_BC, AB, AB_C](
    pBC: Prd[B, C, BC],
    pA_BC: Prd[A, BC, A_BC],
    pAB: Prd[A, B, AB],
    pAB_C: Prd[AB, C, AB_C],
  ): A_BC -> AB_C

  /** Given two witnesses that `P` and `Q` are each the tensor of `A` and `B`,
    * prove that `P` and `Q` are equal.
    */
  def tensorUniq[A, B, P, Q](p: Prd[A, B, P], q: Prd[A, B, Q]): P =:= Q

  def wfst[X, Y](f: X -> Y)[Z](using z: Obj[Z])(using x: Obj[X], y: Obj[Y])[P, Q](
    pSrc: Prd[X, Z, P],
    pTgt: Prd[Y, Z, Q],
  ): P -> Q =
    wpar(f, id[Z])(pSrc, pTgt)

  def wsnd[X](using x: Obj[X])[Y, Z](f: Y -> Z)(using y: Obj[Y], z: Obj[Z])[P, Q](
    pSrc: Prd[X, Y, P],
    pTgt: Prd[X, Z, Q],
  ): P -> Q =
    wpar(id[X], f)(pSrc, pTgt)
}
