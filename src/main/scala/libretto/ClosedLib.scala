package libretto

class ClosedLib[DSL <: ClosedDSL](dsl0: DSL) extends CoreLib[DSL](dsl0) { lib =>
  import dsl._

  /** Function object (internal hom) is contravariant in the input type. */
  def input[C]: ContraFunctor[* =⚬ C] = new ContraFunctor[* =⚬ C] {
    def lift[A, B](f: A -⚬ B): (B =⚬ C) -⚬ (A =⚬ C) =
      id                       [(B =⚬ C) |*| A]
        .in.snd(f)          .to[(B =⚬ C) |*| B]
        .andThen(eval)      .to[C]
        .as[((B =⚬ C) |*| A) -⚬ C]
        .curry
  }

  /** Function object (internal hom) is covariant in the output type. */
  def output[A]: Functor[A =⚬ *] = new Functor[A =⚬ *] {
    def lift[B, C](f: B -⚬ C): (A =⚬ B) -⚬ (A =⚬ C) =
      id                       [(A =⚬ B) |*| A]
        .andThen(eval)      .to[B]
        .andThen(f)         .to[C]
        .as[((A =⚬ B) |*| A) -⚬ C]
        .curry
  }

  implicit class ClosedLinearFunctionOps[A, B](self: A -⚬ B) {
    def curry[A1, A2](implicit ev: A =:= (A1 |*| A2)): A1 -⚬ (A2 =⚬ B) =
      dsl.curry(ev.substituteCo[* -⚬ B](self))

    def uncurry[B1, B2](implicit ev: B =:= (B1 =⚬ B2)): (A |*| B1) -⚬ B2 =
      dsl.uncurry(ev.substituteCo(self))
  }

  implicit class FocusedFunctionOutputOnFunctionCo[A, F[_], B1, B2](f: FocusedFunctionOutputCo[A, F, B1 =⚬ B2]) {
    def input: FocusedFunctionOutputContra[A, λ[x => F[x =⚬ B2]], B1] =
      f.zoomContra(lib.input[B2])

    def output: FocusedFunctionOutputCo[A, λ[x => F[B1 =⚬ x]], B2] =
      f.zoomCo(lib.output[B1])
  }

  implicit class FocusedFunctionOutputOnFunctionContra[A, F[_], B1, B2](f: FocusedFunctionOutputContra[A, F, B1 =⚬ B2]) {
    def input: FocusedFunctionOutputCo[A, λ[x => F[x =⚬ B2]], B1] =
      f.zoomContra(lib.input[B2])

    def output: FocusedFunctionOutputContra[A, λ[x => F[B1 =⚬ x]], B2] =
      f.zoomCo(lib.output[B1])
  }

  def zapPremises[A, Ā, B, C](implicit ev: Dual[A, Ā]): ((A =⚬ B) |*| (Ā =⚬ C)) -⚬ (B |*| C) = {
    id                              [  (A =⚬ B) |*| (Ā =⚬ C)                ]
      .introSnd(ev.lInvert)      .to[ ((A =⚬ B) |*| (Ā =⚬ C)) |*| (Ā |*| A) ]
      .in.snd(swap)              .to[ ((A =⚬ B) |*| (Ā =⚬ C)) |*| (A |*| Ā) ]
      .andThen(IXI)              .to[ ((A =⚬ B) |*| A) |*| ((Ā =⚬ C) |*| Ā) ]
      .andThen(par(eval, eval))  .to[        B         |*|        C         ]
  }

  /** Given `A` and `B` concurrently (`A |*| B`), we can suggest that `A` be consumed before `B`
    * by turning it into `Ā =⚬ B`, where `Ā` is the dual of `A`.
    */
  def unveilSequentially[A, Ā, B](implicit ev: Dual[A, Ā]): (A |*| B) -⚬ (Ā =⚬ B) =
    id[(A |*| B) |*| Ā]           .to[ (A |*|  B) |*| Ā  ]
      .timesAssocLR               .to[  A |*| (B  |*| Ā) ]
      .in.snd(swap)               .to[  A |*| (Ā  |*| B) ]
      .timesAssocRL               .to[ (A |*|  Ā) |*| B  ]
      .elimFst(ev.rInvert)        .to[                B  ]
      .as[ ((A |*| B) |*| Ā) -⚬ B ]
      .curry

  /** Make a function `A =⚬ B` ''"absorb"'' a `C` and return it as part of its output, i.e. `A =⚬ (B |*| C)`. */
  def absorbR[A, B, C]: ((A =⚬ B) |*| C) -⚬ (A =⚬ (B |*| C)) =
    id[((A =⚬ B) |*| C) |*| A]  .to[ ((A =⚬ B) |*| C) |*| A ]
      .timesAssocLR             .to[ (A =⚬ B) |*| (C |*| A) ]
      .in.snd(swap)             .to[ (A =⚬ B) |*| (A |*| C) ]
      .timesAssocRL             .to[ ((A =⚬ B) |*| A) |*| C ]
      .in.fst(eval)             .to[        B         |*| C ]
      .as[ (((A =⚬ B) |*| C) |*| A) -⚬ (B |*| C) ]
      .curry
}
