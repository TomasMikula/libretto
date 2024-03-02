package kindville.lib

import kindville.{::, Box, TNil}

opaque type Forall[K, F <: AnyKind] =
  Box[
    F :: TNil,
    Forall.Code[K],
  ]

object Forall {
  private[lib] type Code = [K] =>>
    [⋅⋅[_]] =>>
      [F0[_]] =>>
        [A <: ⋅⋅[K]] => Unit => F0[⋅⋅[A]]

  transparent inline def apply[K, F <: AnyKind]: Nothing => Forall[K, F] =
    Box.pack[F :: TNil, Code[K]]

  extension [K, F <: AnyKind](f: Forall[K, F])
    transparent inline def at: Any =
      Box.unpack(f)
}
