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

  def wpar[A1, A2, B1, B2, P, Q](
    f1: A1 -> B1,
    f2: A2 -> B2,
  )(using
    a1: Obj[A1], a2: Obj[A2],
    b1: Obj[B1], b2: Obj[B2],
  )(
    pSrc: Prd[A1, A2, P],
    pTgt: Prd[B1, B2, Q],
  ): P -> Q

  def wassocLR[A, B, C, AB, BC, S, T](
    a: Obj[A], b: Obj[B], c: Obj[C],
  )(
    pAB: Prd[A, B, AB],
    pBC: Prd[B, C, BC],
    pAB_C: Prd[AB, C, S],
    pA_BC: Prd[A, BC, T],
  ): S -> T

  def wassocRL[A, B, C, AB, BC, S, T](
    a: Obj[A], b: Obj[B], c: Obj[C],
  )(
    pAB: Prd[A, B, AB],
    pBC: Prd[B, C, BC],
    pAB_C: Prd[AB, C, S],
    pA_BC: Prd[A, BC, T],
  ): T -> S

  /** Given two witnesses that `P` and `Q` are each the tensor of `A` and `B`,
    * prove that `P` and `Q` are equal.
    */
  def tensorUniq[A, B, P, Q](p: Prd[A, B, P], q: Prd[A, B, Q]): P =:= Q

  def wfst[X, Y, Z, P, Q](f: X -> Y, z: Obj[Z])(using x: Obj[X], y: Obj[Y])(
    pSrc: Prd[X, Z, P],
    pTgt: Prd[Y, Z, Q],
  ): P -> Q =
    given Obj[Z] = z
    wpar(f, id(z))(pSrc, pTgt)

  def wsnd[X, Y, Z, P, Q](x: Obj[X], f: Y -> Z)(using y: Obj[Y], z: Obj[Z])(
    pSrc: Prd[X, Y, P],
    pTgt: Prd[X, Z, Q],
  ): P -> Q =
    given Obj[X] = x
    wpar(id(x), f)(pSrc, pTgt)
}
