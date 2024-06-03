package libretto.lambda

/** A semigroupal category (i.e. monoidal without a unit object) with _coproduct_ as the tensor (product).  */
trait CocartesianSemigroupalCategory[->[_, _], <+>[_, _]]
extends SemigroupalCategory[->, <+>] {
  def injectL[A, B]: A -> (A <+> B)
  def injectR[A, B]: B -> (A <+> B)
  def either[A, B, C](f: A -> C, g: B -> C): (A <+> B) -> C

  override def par[A1, A2, B1, B2](f1: A1 -> B1, f2: A2 -> B2): (A1 <+> A2) -> (B1 <+> B2) =
    either(andThen(f1, injectL), andThen(f2, injectR))

  override def assocLR[A, B, C]: ((A <+> B) <+> C) -> (A <+> (B <+> C)) =
    either(either(injectL, andThen(injectL, injectR)), andThen(injectR, injectR))

  override def assocRL[A, B, C]: (A <+> (B <+> C)) -> ((A <+> B) <+> C) =
    either(andThen(injectL, injectL), either(andThen(injectR, injectL), injectR))
}
