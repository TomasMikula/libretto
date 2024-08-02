package libretto.closed

import libretto.puro.PuroLib

object ClosedLib {
  def apply(
    dsl: ClosedDSL,
    puroLib: PuroLib[dsl.type],
  )
  : ClosedLib[dsl.type, puroLib.type] =
    new ClosedLib(dsl, puroLib)
}

class ClosedLib[
  DSL <: ClosedDSL,
  PLib <: PuroLib[DSL],
](
  val dsl: DSL,
  val puroLib: PLib & PuroLib[dsl.type],
) { lib =>
  import dsl.*
  import puroLib.*

  /** Function object (internal hom) is contravariant in the input type. */
  def input[C]: ContraFunctor[[x] =>> x =⚬ C] =
    new ContraFunctor[[x] =>> x =⚬ C] {
      override val category =
        dsl.category

      override def lift[A, B](f: A -⚬ B): (B =⚬ C) -⚬ (A =⚬ C) =
        id                         [ (B =⚬ C) |*| A ]
          .>.snd(f)             .to[ (B =⚬ C) |*| B ]
          .>(eval)              .to[       C        ]
          .as[ ((B =⚬ C) |*| A)  -⚬        C        ]
          .curry
    }

  /** Function object (internal hom) is covariant in the output type. */
  def output[A]: Functor[[x] =>> A =⚬ x] =
    new Functor[[x] =>> A =⚬ x] {
      override val category =
        dsl.category

      override def lift[B, C](f: B -⚬ C): (A =⚬ B) -⚬ (A =⚬ C) =
        out(f)
    }

  extension [A, B](f: A -⚬ B) {
    def curry[A1, A2](using ev: A =:= (A1 |*| A2)): A1 -⚬ (A2 =⚬ B) =
      dsl.curry(ev.substituteCo[λ[x => x -⚬ B]](f))

    def uncurry[B1, B2](using ev: B =:= (B1 =⚬ B2)): (A |*| B1) -⚬ B2 =
      dsl.uncurry(ev.substituteCo(f))
  }

  extension [F[_], A, B](f: FocusedCo[F, A =⚬ B]) {
    def input: FocusedContra[λ[x => F[x =⚬ B]], A] =
      f.zoomContra(lib.input[B])

    def output: FocusedCo[λ[x => F[A =⚬ x]], B] =
      f.zoomCo(lib.output[A])
  }

  extension [F[_], A, B](f: FocusedContra[F, A =⚬ B]) {
    def input: FocusedCo[λ[x => F[x =⚬ B]], A] =
      f.zoomContra(lib.input[B])

    def output: FocusedContra[λ[x => F[A =⚬ x]], B] =
      f.zoomCo(lib.output[A])
  }

  def zapPremises[A, Ā, B, C](using ev: Dual[A, Ā]): ((A =⚬ B) |*| (Ā =⚬ C)) -⚬ (B |*| C) = {
    id                              [  (A =⚬ B) |*| (Ā =⚬ C)                ]
      .>(introSnd(ev.lInvert))   .to[ ((A =⚬ B) |*| (Ā =⚬ C)) |*| (Ā |*| A) ]
      .>.snd(swap)               .to[ ((A =⚬ B) |*| (Ā =⚬ C)) |*| (A |*| Ā) ]
      .>(IXI)                    .to[ ((A =⚬ B) |*| A) |*| ((Ā =⚬ C) |*| Ā) ]
      .>(par(eval, eval))        .to[        B         |*|        C         ]
  }

  /** Given `A` and `B` concurrently (`A |*| B`), we can suggest that `A` be consumed before `B`
    * by turning it into `Ā =⚬ B`, where `Ā` is the dual of `A`.
    */
  def unveilSequentially[A, Ā, B](using ev: Dual[A, Ā]): (A |*| B) -⚬ (Ā =⚬ B) =
    id[(A |*| B) |*| Ā]           .to[ (A |*|  B) |*| Ā  ]
      .>(assocLR)                 .to[  A |*| (B  |*| Ā) ]
      .>.snd(swap)                .to[  A |*| (Ā  |*| B) ]
      .>(assocRL)                 .to[ (A |*|  Ā) |*| B  ]
      .>(elimFst(ev.rInvert))     .to[                B  ]
      .as[ ((A |*| B) |*| Ā) -⚬ B ]
      .curry

  /** Make a function `A =⚬ B` ''"absorb"'' a `C` and return it as part of its output, i.e. `A =⚬ (B |*| C)`. */
  def absorbR[A, B, C]: ((A =⚬ B) |*| C) -⚬ (A =⚬ (B |*| C)) =
    id[((A =⚬ B) |*| C) |*| A]  .to[ ((A =⚬ B) |*| C) |*| A ]
      .>(assocLR)               .to[ (A =⚬ B) |*| (C |*| A) ]
      .>.snd(swap)              .to[ (A =⚬ B) |*| (A |*| C) ]
      .>(assocRL)               .to[ ((A =⚬ B) |*| A) |*| C ]
      .>.fst(eval)              .to[        B         |*| C ]
      .as[ (((A =⚬ B) |*| C) |*| A) -⚬ (B |*| C) ]
      .curry
}
