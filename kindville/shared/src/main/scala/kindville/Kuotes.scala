package kindville

sealed trait Kuotes[⋅⋅[_]] {
  /** Disguises `T` from the real world as `U` in the coded world.
   *
   * It is required that `t` qualifies as an expression of type `《U》` (decoding of `U`).
   */
  def disguise[T](t: T)[U]: U

  // temporary, to test inline expansion to `disguise`
  transparent inline def disguise1[T](t: T)[U]: U =
    disguise[T](t)[U]
}

object Kuotes {
  extension [⋅⋅[_], T](t: T)(using kuotes: Kuotes[⋅⋅])
    // TODO: investigate why not inlined
    inline def disguiseAs[U]: U =
      kuotes.disguise[T](t)[U]
}
