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
}

object Kuotes {
  extension [⋅⋅[_], T](t: T)(using kuotes: Kuotes[⋅⋅])
    // TODO: investigate why not inlined
    inline def spliceAs[U]: U =
      kuotes.splice[T](t)[U]
}
