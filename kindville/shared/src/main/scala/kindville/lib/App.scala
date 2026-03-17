package kindville.lib

import kindville.*

/** Represents G[X], i.e. G applied to X. */
opaque type App[K, G <: AnyKind, X <: AnyKind] =
  Box[App.Code[K], G :: X :: TNil]

object App {
  type Code[K] = [⋅⋅[_]] =>> [G0[_ <: ⋅⋅[K]], X0 <: ⋅⋅[K]] =>> G0[X0]

  /** Returns G[A..] => App[K, G, A] */
  transparent inline def pack[K, G <: AnyKind, A <: AnyKind] =
    // basically just Box.pack, but need to re-encode for the result to return App instead of Box
    decodeT[G :: A :: TNil](
      [⋅⋅[_]] => kuotes ?=> [G0[_ <: ⋅⋅[K]], A0 <: ⋅⋅[K]] => () =>
        val pack: G0[A0] => App[K, G, A] =
          kuotes.splice(Box.pack[Code[K], G :: A :: TNil])
        pack
    )

  /** Returns G[A]. */
  transparent inline def unpack[K, G <: AnyKind, A <: AnyKind](a: App[K, G, A]) =
    Box.unpack(a)
}
