package libretto.lambda

/** A symmetric semigroupal category on all Scala types, where the monoidal product (tensor)
  * is not given as a fixed binary type constructor, but is *witnessed* (hence "W" in WSemigroupal)
  * by a ternary relation `Prd[A, B, P]` that `P` is the tensor of `A` and `B`.
  *
  * A non-narrow (i.e. all Scala types are objects) extension of [[NarrowSymmetricWSemigroupalCategory]].
  *
  * @tparam ->   morphism of the category
  * @tparam Prd  witnesses tensor formation: `Prd[A, B, P]` means that `P` is the tensor of `A` and `B`.
  */
trait SymmetricWSemigroupalCategory[->[_, _], Prd[_, _, _]]
  extends NarrowSymmetricWSemigroupalCategory[[x] =>> Unit, ->, Prd]
  with WSemigroupalCategory[->, Prd]
{
  import NarrowWSemigroupalCategory.*

  /** Swap the two components, witnessed variant. */
  def wswap[A, B, P, Q](
    p: Prd[A, B, P],
    q: Prd[B, A, Q],
  ): P -> Q =
    iswap[\[A], \[B]].extract[P, Q](
      PrdN.lift(p)(using (), ()),
      PrdN.lift(q)(using (), ()),
    )

  /** Interchange second and third component, ((A×B)×C) -> ((A×C)×B), witnessed variant. */
  def w_ix[A, B, C, AB, AB_C, AC, AC_B](
    pAB:   Prd[A, B, AB],
    pAB_C: Prd[AB, C, AB_C],
    pAC:   Prd[A, C, AC],
    pAC_B: Prd[AC, B, AC_B],
  ): AB_C -> AC_B =
    i_ix[\[A], \[B], \[C]].extract[AB_C, AC_B](
      PrdN(pAB_C)(PrdN.lift(pAB)(using (), ()), PrdN.atom[C](using ())),
      PrdN(pAC_B)(PrdN.lift(pAC)(using (), ()), PrdN.atom[B](using ())),
    )

  /** Interchange first and second component, A×(B×C) -> B×(A×C), witnessed variant. */
  def w_xi[A, B, C, BC, A_BC, AC, B_AC](
    pBC:   Prd[B, C, BC],
    pA_BC: Prd[A, BC, A_BC],
    pAC:   Prd[A, C, AC],
    pB_AC: Prd[B, AC, B_AC],
  ): A_BC -> B_AC =
    i_xi[\[A], \[B], \[C]].extract[A_BC, B_AC](
      PrdN(pA_BC)(PrdN.atom[A](using ()), PrdN.lift(pBC)(using (), ())),
      PrdN(pB_AC)(PrdN.atom[B](using ()), PrdN.lift(pAC)(using (), ())),
    )

  /** Interchange inner components, ((A×B)×(C×D)) -> ((A×C)×(B×D)), witnessed variant. */
  def w_ixi[A, B, C, D, CD, AB, AB_CD, AC, BD, AC_BD](
    pAB:    Prd[A, B, AB],
    pCD:    Prd[C, D, CD],
    pAB_CD: Prd[AB, CD, AB_CD],
    pAC:    Prd[A, C, AC],
    pBD:    Prd[B, D, BD],
    pAC_BD: Prd[AC, BD, AC_BD],
  ): AB_CD -> AC_BD =
    i_ixi[\[A], \[B], \[C], \[D]].extract[AB_CD, AC_BD](
      PrdN(pAB_CD)(PrdN.lift(pAB)(using (), ()), PrdN.lift(pCD)(using (), ())),
      PrdN(pAC_BD)(PrdN.lift(pAC)(using (), ()), PrdN.lift(pBD)(using (), ())),
    )

  override def wswap[A, B](using wa: Unit, wb: Unit)[P, Q](
    p: Prd[A, B, P],
    q: Prd[B, A, Q],
  ): P -> Q =
    wswap[A, B, P, Q](p, q)

  override def w_ix[A, B, C](using wa: Unit, wb: Unit, wc: Unit)[AB, AB_C, AC, AC_B](
    pAB:   Prd[A, B, AB],
    pAB_C: Prd[AB, C, AB_C],
    pAC:   Prd[A, C, AC],
    pAC_B: Prd[AC, B, AC_B],
  ): AB_C -> AC_B =
    w_ix[A, B, C, AB, AB_C, AC, AC_B](pAB, pAB_C, pAC, pAC_B)

  override def w_xi[A, B, C](using wa: Unit, wb: Unit, wc: Unit)[BC, A_BC, AC, B_AC](
    pBC:   Prd[B, C, BC],
    pA_BC: Prd[A, BC, A_BC],
    pAC:   Prd[A, C, AC],
    pB_AC: Prd[B, AC, B_AC],
  ): A_BC -> B_AC =
    w_xi[A, B, C, BC, A_BC, AC, B_AC](pBC, pA_BC, pAC, pB_AC)

  override def w_ixi[A, B, C, D](using wa: Unit, wb: Unit, wc: Unit, wd: Unit)[CD, AB, AB_CD, AC, BD, AC_BD](
    pAB:    Prd[A, B, AB],
    pCD:    Prd[C, D, CD],
    pAB_CD: Prd[AB, CD, AB_CD],
    pAC:    Prd[A, C, AC],
    pBD:    Prd[B, D, BD],
    pAC_BD: Prd[AC, BD, AC_BD],
  ): AB_CD -> AC_BD =
    w_ixi[A, B, C, D, CD, AB, AB_CD, AC, BD, AC_BD](pAB, pCD, pAB_CD, pAC, pBD, pAC_BD)
}