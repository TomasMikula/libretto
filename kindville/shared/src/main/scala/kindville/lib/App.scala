package kindville.lib

import kindville.*

/** Represents G[X], i.e. G applied to X. */
opaque type App[K, G <: AnyKind, X <: AnyKind] =
  Box[App.Code[K], G :: X :: TNil]

object App {
  type Code[K] = [⋅⋅[_]] =>> [G0[_ <: ⋅⋅[K]], X0 <: ⋅⋅[K]] =>> G0[X0]

  /** Returns G[A..] => App[K, G, A] */
  transparent inline def pack[K, G <: AnyKind, A <: AnyKind] =
    // basically just Box.pack, but need the result to formally return App instead of Box
    decodeT[G :: A :: TNil](
      [⋅⋅[_]] => kuotes ?=> [G0[_ <: ⋅⋅[K]], A0 <: ⋅⋅[K]] => () =>
        val pack: G0[A0] => App[K, G, A] =
          kuotes.splice(Box.pack[Code[K], G :: A :: TNil])
        pack
    )

    /** Pack locally within the scope of [[r]], where parameter [[A0]] can be expanded to (abstract) type(s) of the correct kind(s),
     *  even without compiletime knowledge (hence "dynamic") of the actual type argument(s) it stands for.
     */
  inline def packDynamic[⋅⋅[_], ⋅⋅⋅[_], K, G0[_ <: ⋅⋅[K]], A0 <: ⋅⋅[K]](ga: G0[A0])(using k: Kuotes.Rekindle[⋅⋅, ⋅⋅⋅]): App[K, G0, ⋅⋅⋅[A0]] =
    k.pack(ga)[Code[K], G0 :: ⋅⋅⋅[A0] :: TNil]

  /** Returns `[F[..], A..] => F[A..] => App[K, F, A]`. */
  transparent inline def packer[K] =
    // basically just Box.packer, but need the result to formally return App instead of Box
    decode(
      [⋅⋅[_]] => k ?=>
        val packer: [F0[_ <: ⋅⋅[K]], A0 <: ⋅⋅[K]] => F0[A0] => App[K, F0, ⋅⋅[A0]] =
          k.splice(Box.packer[Code[K]])
        packer
    )

  extension [K, G <: AnyKind, A <: AnyKind](a: App[K, G, A]) {
    /** Returns G[A]. */
    transparent inline def unpack =
      Box.unpack(a)
  }

  extension [⋅⋅[_], ⋅⋅⋅[_], K, G0[_ <: ⋅⋅[K]], A0 <: ⋅⋅[K]](a: App[K, G0, ⋅⋅⋅[A0]])(using r: Kuotes.Rekindle[⋅⋅, ⋅⋅⋅]) {

    /** Unpack locally within the scope of [[r]], where parameter [[A0]] can be expanded to (abstract) type(s) of the correct kind(s),
     *  even without compiletime knowledge (hence "dynamic") of the actual type argument(s) it stands for.
     */
    inline def unpackDynamic: G0[A0] =
      r.unpack[Code[K], G0 :: ⋅⋅⋅[A0] :: TNil](a)
  }

  /** Returns `[F[..], A..] => App[K, F, A] => F[A..]`. */
  transparent inline def unpacker[K] =
    // basically just Box.unpacker, but need the result to formally take App instead of Box
    decode(
      [⋅⋅[_]] => k ?=>
        val unpacker: [F0[_ <: ⋅⋅[K]], A0 <: ⋅⋅[K]] => App[K, F0, ⋅⋅[A0]] => F0[A0] =
          k.splice(Box.unpacker[Code[K]])
        unpacker
    )
}
