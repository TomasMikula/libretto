package kindville

sealed trait Kuotes[⋅⋅[_]] {
  /** Disguises `T`, which must be equal to `《Code》[As⋅⋅]`, as `U`, which must be equal to `Code[Ps⋅⋅]`, where
   *  - `《t》` is the interpretation (decoding) of type `t` under `⋅⋅`,
   *  - `[ts⋅⋅]` is a list of types `ts = t1 :: ... :: TNil` spread as individual type arguments `[t1, ...]`.
   */
  def disguise[T](t: T)[Code <: AnyKind, As, Ps, U]: U

  // temporary, to test inline expansion to `disguise`
  transparent inline def disguise1[T](t: T)[Code <: AnyKind, As, Ps, U]: U =
    disguise[T](t)[Code, As, Ps, U]
}

object Kuotes {
  extension [⋅⋅[_], T](t: T)(using kuotes: Kuotes[⋅⋅])
    // TODO: investigate why not inlined
    inline def disguiseAs[Code <: AnyKind, As, Ps, U]: U =
      kuotes.disguise[T](t)[Code, As, Ps, U]
}
