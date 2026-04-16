package kindville.lib

import kindville.*

/** Represents G[X], i.e. G applied to X. */
opaque type App[K, G <: AnyKind, X <: AnyKind] =
  Box[App.Code[K], G :: X :: TNil]

object App {
  type Code[K] = [⋅⋅[_]] =>> [G0[_ <: ⋅⋅[K]], X0 <: ⋅⋅[K]] =>> G0[X0]

  /** Returns G[A..] => App[K, G, A] */
  transparent inline def pack[K, G <: AnyKind, A <: AnyKind] =
    // basically just Box.pack, but need to re-encode for the result to formally return App instead of Box
    decodeT[G :: A :: TNil](
      [⋅⋅[_]] => kuotes ?=> [G0[_ <: ⋅⋅[K]], A0 <: ⋅⋅[K]] => () =>
        val pack: G0[A0] => App[K, G, A] =
          kuotes.splice(Box.pack[Code[K], G :: A :: TNil])
        pack
    )

  /** Returns `[F[..], A..] => F[A..] => App[K, F, A]`. */
  transparent inline def packer[K] =
    // basically just Box.packer, but need the result to formally return App instead of Box
    decode(
      [⋅⋅[_]] => k ?=>
        val packer: [F0[_ <: ⋅⋅[K]], A0 <: ⋅⋅[K]] => F0[A0] => App[K, F0, ⋅⋅[A0]] =
          k.splice(Box.packer[Code[K]])
        [F0[_ <: ⋅⋅[K]], A0 <: ⋅⋅[K]] => (fa: F0[A0]) =>
          packer(fa) : App[K, F0, ⋅⋅[A0]]
    )

  /** Returns G[A]. */
  transparent inline def unpack[K, G <: AnyKind, A <: AnyKind](a: App[K, G, A]) =
    Box.unpack(a)

  /** Returns `[F[..], A..] => App[K, F, A] => F[A..]`. */
  transparent inline def unpacker[K] =
    // basically just Box.unpacker, but need the result to formally take App instead of Box
    decode(
      [⋅⋅[_]] => k ?=>
        val unpacker: [F0[_ <: ⋅⋅[K]], A0 <: ⋅⋅[K]] => App[K, F0, ⋅⋅[A0]] => F0[A0] =
          k.splice(Box.unpacker[Code[K]])
        [F0[_ <: ⋅⋅[K]], A0 <: ⋅⋅[K]] => (fa: App[K, F0, ⋅⋅[A0]]) =>
          unpacker(fa) : F0[A0]
    )
}
