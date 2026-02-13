package kindville.lib

import kindville.*

opaque type Forall[K, F <: AnyKind] =
  Box[Forall.Code[K], F :: TNil]

object Forall {
  private[lib] type Code = [K] =>>
    [⋅⋅[_]] =>>
      [F0[_ <: ⋅⋅[K]]] =>>
        [A <: ⋅⋅[K]] => Unit => F0[A]

  /** Returns `([A...] => Unit => F[A...]) => Forall[K, F]`. */
  transparent inline def apply[K, F <: AnyKind]: Any =
    decodeExpr[F :: TNil](
      [⋅⋅[_], F0[_ <: ⋅⋅[K]]] =>
        (pack: ([A <: ⋅⋅[K]] => Unit => F0[A]) => Box[Code[K], F :: TNil]) =>
          (f: [A <: ⋅⋅[K]] => Unit => F0[A]) =>
            pack(f): Forall[K, F]
    )(
      Box.pacK[(K ->> *) :: TNil, Code[K], F :: TNil]
    )

  extension [K, F <: AnyKind](f: Forall[K, F])
    transparent inline def at: Any =
      Box.unpack(f)
}
