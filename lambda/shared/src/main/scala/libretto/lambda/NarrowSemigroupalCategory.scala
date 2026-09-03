package libretto.lambda

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

  def assocLR[A, B, C](a: Obj[A], b: Obj[B], c: Obj[C]): ((A |*| B) |*| C) -> (A |*| (B |*| C))
  def assocRL[A, B, C](a: Obj[A], b: Obj[B], c: Obj[C]): (A |*| (B |*| C)) -> ((A |*| B) |*| C)

  override def wtensor[A, B, P](wa: Obj[A], wb: Obj[B])(p: (A |*| B) =:= P): Obj[P] =
    p.substituteCo[Obj](tensor(wa, wb))

  override def wpar[A1, A2, B1, B2, P, Q](
    f1: A1 -> B1,
    f2: A2 -> B2,
  )(using
    a1: Obj[A1], a2: Obj[A2],
    b1: Obj[B1], b2: Obj[B2],
  )(
    pSrc: (A1 |*| A2) =:= P,
    pTgt: (B1 |*| B2) =:= Q,
  ): P -> Q = {
    val g: (A1 |*| A2) -> (B1 |*| B2) = narrowPar(f1, f2)
    pTgt.substituteCo[[X] =>> P -> X](pSrc.substituteCo[[X] =>> X -> (B1 |*| B2)](g))
  }

  override def wassocLR[A, B, C, AB, BC, S, T](
    a: Obj[A], b: Obj[B], c: Obj[C],
  )(
    pAB: (A |*| B) =:= AB,
    pBC: (B |*| C) =:= BC,
    pAB_C: (AB |*| C) =:= S,
    pA_BC: (A |*| BC) =:= T,
  ): S -> T = {
    val g0: ((A |*| B) |*| C) -> (A |*| (B |*| C)) = assocLR(a, b, c)
    val g1: S -> (A |*| (B |*| C)) =
      pAB_C.substituteCo[[X] =>> X -> (A |*| (B |*| C))](
        pAB.substituteCo[[X] =>> (X |*| C) -> (A |*| (B |*| C))](g0),
      )
    pA_BC.substituteCo[[X] =>> S -> X](
      pBC.substituteCo[[X] =>> S -> (A |*| X)](g1),
    )
  }

  override def wassocRL[A, B, C, AB, BC, S, T](
    a: Obj[A], b: Obj[B], c: Obj[C],
  )(
    pAB: (A |*| B) =:= AB,
    pBC: (B |*| C) =:= BC,
    pAB_C: (AB |*| C) =:= S,
    pA_BC: (A |*| BC) =:= T,
  ): T -> S = {
    val g0: (A |*| (B |*| C)) -> ((A |*| B) |*| C) = assocRL(a, b, c)
    val g1: T -> ((A |*| B) |*| C) =
      pA_BC.substituteCo[[X] =>> X -> ((A |*| B) |*| C)](
        pBC.substituteCo[[X] =>> (A |*| X) -> ((A |*| B) |*| C)](g0),
      )
    pAB_C.substituteCo[[X] =>> T -> X](
      pAB.substituteCo[[X] =>> T -> (X |*| C)](g1),
    )
  }

  override def tensorUniq[A, B, P, Q](
    p: (A |*| B) =:= P,
    q: (A |*| B) =:= Q,
  ): P =:= Q =
    p.flip.andThen(q)

  def fst[X, Y, Z](f: X -> Y, z: Obj[Z])(using x: Obj[X], y: Obj[Y]): (X |*| Z) -> (Y |*| Z) =
    given Obj[Z] = z
    narrowPar(f, id(z))

  def snd[X, Y, Z](x: Obj[X], f: Y -> Z)(using y: Obj[Y], z: Obj[Z]): (X |*| Y) -> (X |*| Z) =
    given Obj[X] = x
    narrowPar(id(x), f)
}
