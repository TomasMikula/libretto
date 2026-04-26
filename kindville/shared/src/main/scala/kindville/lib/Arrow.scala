package kindville.lib

import kindville.*

/** Represents `F[A, B]`. */
opaque type Arrow[K, F <: AnyKind, A <: AnyKind, B <: AnyKind] =
  Box[Arrow.Code[K], F :: A :: B :: TNil]

object Arrow {
  type Code[K] =
    [⋅⋅[_]] =>> [
      F[_ <: ⋅⋅[K], _ <: ⋅⋅[K]],
      A <: ⋅⋅[K],
      B <: ⋅⋅[K],
    ] =>>
      F[A, B]

  /** Returns `[F[_, _], A, B] => F[A, B] => Arrow[K, F, A, B]` */
  transparent inline def packer[K] =
    // basically just Box.packer[Code[K]], but need the result to formally return `Arrow[K, F, A, B]` instead of `Box`
    decode(
      [⋅⋅[_]] => k ?=>
        val packer: [F[_ <: ⋅⋅[K], _ <: ⋅⋅[K]], A <: ⋅⋅[K], B <: ⋅⋅[K]] => F[A, B] => Arrow[K, F, ⋅⋅[A], ⋅⋅[B]] =
          k.splice(Box.packer[Code[K]])
        packer
    )

  /** Returns `F[A, B] => Arrow[K, F, A, B]`. */
  transparent inline def pack[K, F <: AnyKind, A <: AnyKind, B <: AnyKind] =
    // basically just Box.pack, but need the result to formally return an Arrow instead of Box
    decodeT[F :: A :: B :: TNil](
      [⋅⋅[_]] => (k: Kuotes[⋅⋅]) ?=> [F0[_ <: ⋅⋅[K], _ <: ⋅⋅[K]], A0 <: ⋅⋅[K], B0 <: ⋅⋅[K]] => () =>
        val pack: F0[A0, B0] => Arrow[K, F, A, B] =
          k.splice(Box.pack[Code[K], F :: A :: B :: TNil])
        pack
    )

  /** Returns `[F[_, _], A, B] => Arrow[K, F, A, B] => F[A, B]`. */
  transparent inline def unpacker[K] =
    // basically just Box.unpacker[Code[K]], but need the result to formally take `Arrow[K, F, A, B]` instead of `Box`
    decode(
      [⋅⋅[_]] => k ?=>
        val unpacker: [F[_ <: ⋅⋅[K], _ <: ⋅⋅[K]], A <: ⋅⋅[K], B <: ⋅⋅[K]] => Arrow[K, F, ⋅⋅[A], ⋅⋅[B]] => F[A, B] =
          k.splice(Box.unpacker[Code[K]])
        unpacker
    )

  extension [K, F <: AnyKind, A <: AnyKind, B <: AnyKind](a: Arrow[K, F, A, B]) {
    /** Returns `F[A, B]`. */
    transparent inline def unpack =
      Box.unpack(a)
  }

  sealed trait Opt[K, F <: AnyKind, A <: AnyKind, B <: AnyKind]

  object Opt {
    case class None[K, F <: AnyKind, A <: AnyKind]() extends Opt[K, F, A, A]
    case class Some[K, F <: AnyKind, A <: AnyKind, B <: AnyKind](arrow: Arrow[K, F, A, B]) extends Opt[K, F, A, B]
  }
}
