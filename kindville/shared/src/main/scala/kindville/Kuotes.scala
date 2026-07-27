package kindville

sealed trait Kuotes[⋅⋅[_]] {
  /** Provides a witness that within the scope of these [[Kuotes]], the type(s) `A` is represented as `A0`. */
  def locallyEquals[A <: AnyKind, A0]: A =~= ⋅⋅[A0]

  /** Disguises `T` from the real world as `U` in the coded world.
   *
   * It is required that `t` qualifies as an expression of type `《U》` (decoding of `U`).
   */
  def splice[T](t: T)[U]: U

  // temporary, to test inline expansion to `splice`
  transparent inline def disguise[T](t: T)[U]: U =
    splice[T](t)[U]

  /** Introduces a local scope in which
    *  - type parameters (like `A0 <: ⋅⋅[K]`) of the surrounding [[decodeT]] can be expanded even without compiletime knowledge of the corresponding type argument `A`.
    *    Such parameters are expanded to locally forged types of the right kinds.
    *  - `⋅⋅⋅[A0]` can be used to create a bundle (HList) of the forged types (vs. `⋅⋅[A0]` expanding to the original type argument `A`).
    *
    * Note that the return type `R` is unable to refer to `⋅⋅⋅` or to `A0` when `A0` is not known at compiletime, thus preventing leakage of forged types.
    */
  def rekindle[R](body: [⋅⋅⋅[_]] => Kuotes.Rekindle[⋅⋅, ⋅⋅⋅] ?=> R): R
}

object Kuotes {
  extension [⋅⋅[_], T](t: T)(using kuotes: Kuotes[⋅⋅])
    // TODO: investigate why not inlined
    inline def spliceAs[U]: U =
      kuotes.splice[T](t)[U]


  sealed trait Rekindle[⋅⋅[_], ⋅⋅⋅[_]] {
    def substituteCo[H[_[_]]](x: H[⋅⋅]): H[⋅⋅⋅]
    def substituteContra[H[_[_]]](x: H[⋅⋅⋅]): H[⋅⋅]

    // These could well be already on `Kuotes`, but they only really become usefull when `As` is of the form `⋅⋅⋅[A0] :: ⋅⋅⋅[B0] :: ...`
    // and the types `A`, `B`, ... that they stand for, respectively, are not known at compile-time (otherwise one could use the respective methods on `Box` directly).
    def pack[T](t: T)[Code[⋅[_]] <: AnyKind, As]: Box[Code, As]
    def unpack[Code[⋅[_]] <: AnyKind, As](box: Box[Code, As])[T]: T
  }
}
