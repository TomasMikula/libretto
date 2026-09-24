package libretto.lambda

import libretto.lambda.NarrowWSemigroupalCategory.{\, ×}
import libretto.lambda.util.{Exists, TypeEq}
import libretto.lambda.util.Exists.Indeed
import libretto.lambda.util.TypeEq.Refl

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
  private given Semigroupoid[->] = this

  def iswap[A, B](using PrdN.Intension[A], PrdN.Intension[B]): (A × B) -×> (B × A)

  def wswap[A, B](using
    Obj[A],
    Obj[B],
  )[P, Q](
    p: Prd[A, B, P],
    q: Prd[B, A, Q],
  ): P -> Q =
    iswap[\[A], \[B]]
      .extract[P, Q](PrdN.lift(p), PrdN.lift(q))

  /** Interchange second and third component, ((A×B)×C) -> ((A×C)×B), intensional variant. */
  def i_ix[A, B, C](using
    PrdN.Intension[A],
    PrdN.Intension[B],
    PrdN.Intension[C],
  ): ((A × B) × C) -×> ((A × C) × B) =
    iassocLR[A, B, C] > ipar(iid[A], iswap[B, C]) > iassocRL[A, C, B]

  /** Interchange first and second component, A×(B×C) -> B×(A×C), intensional variant. */
  def i_xi[A, B, C](using
    PrdN.Intension[A],
    PrdN.Intension[B],
    PrdN.Intension[C],
  ): (A × (B × C)) -×> (B × (A × C)) =
    iassocRL[A, B, C] > ipar(iswap[A, B], iid[C]) > iassocLR[B, A, C]

  /** Interchange inner components, ((A×B)×(C×D)) -> ((A×C)×(B×D)), intensional variant. */
  def i_ixi[A, B, C, D](using
    PrdN.Intension[A],
    PrdN.Intension[B],
    PrdN.Intension[C],
    PrdN.Intension[D],
  ): ((A × B) × (C × D)) -×> ((A × C) × (B × D)) =
    iassocLR[A, B, C × D] >
      ipar(iid[A], iassocRL[B, C, D] > ipar(iswap[B, C], iid[D]) > iassocLR[C, B, D]) >
      iassocRL[A, C, B × D]

  /** Interchange second and third component, ((A×B)×C) -> ((A×C)×B), witnessed variant. */
  def w_ix[A, B, C](using
    a: Obj[A], b: Obj[B], c: Obj[C],
  )[AB, AB_C, AC, AC_B](
    pAB:   Prd[A, B, AB],
    pAB_C: Prd[AB, C, AB_C],
    pAC:   Prd[A, C, AC],
    pAC_B: Prd[AC, B, AC_B],
  ): AB_C -> AC_B =
    i_ix[\[A], \[B], \[C]]
      .extract[AB_C, AC_B](
        PrdN(pAB_C)(PrdN.lift(pAB), PrdN.atom[C]),
        PrdN(pAC_B)(PrdN.lift(pAC), PrdN.atom[B]),
      )

  /** Interchange first and second component, A×(B×C) -> B×(A×C), witnessed variant. */
  def w_xi[A, B, C](using
    a: Obj[A], b: Obj[B], c: Obj[C],
  )[BC, A_BC, AC, B_AC](
    pBC:   Prd[B, C, BC],
    pA_BC: Prd[A, BC, A_BC],
    pAC:   Prd[A, C, AC],
    pB_AC: Prd[B, AC, B_AC],
  ): A_BC -> B_AC =
    i_xi[\[A], \[B], \[C]]
      .extract[A_BC, B_AC](
        PrdN(pA_BC)(PrdN.atom[A], PrdN.lift(pBC)),
        PrdN(pB_AC)(PrdN.atom[B], PrdN.lift(pAC)),
      )

  /** Interchange inner components, ((A×B)×(C×D)) -> ((A×C)×(B×D)), witnessed variant. */
  def w_ixi[A, B, C, D](using
    a: Obj[A], b: Obj[B], c: Obj[C], d: Obj[D],
  )[CD, AB, AB_CD, AC, BD, AC_BD](
    pAB:    Prd[A, B, AB],
    pCD:    Prd[C, D, CD],
    pAB_CD: Prd[AB, CD, AB_CD],
    pAC:    Prd[A, C, AC],
    pBD:    Prd[B, D, BD],
    pAC_BD: Prd[AC, BD, AC_BD],
  ): AB_CD -> AC_BD =
    i_ixi[\[A], \[B], \[C], \[D]]
      .extract[AB_CD, AC_BD](
        PrdN(pAB_CD)(PrdN.lift(pAB), PrdN.lift(pCD)),
        PrdN(pAC_BD)(PrdN.lift(pAC), PrdN.lift(pBD)),
      )
}
