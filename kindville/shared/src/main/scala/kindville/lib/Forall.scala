package kindville.lib

import kindville.{::, Box, TNil}

opaque type Forall[K, F <: AnyKind] =
  Box[
    Forall.Code[K],
    F :: TNil,
  ]

object Forall {
  private[lib] type Code = [K] =>>
    [⋅⋅[_]] =>>
      [F0[_]] =>>
        [A <: ⋅⋅[K]] => Unit => F0[A]

  transparent inline def apply[K, F <: AnyKind]: Nothing => Forall[K, F] =
    Box.pack[Code[K], F :: TNil]

  extension [K, F <: AnyKind](f: Forall[K, F])
    transparent inline def at: Any =
      Box.unpack(f)
}
