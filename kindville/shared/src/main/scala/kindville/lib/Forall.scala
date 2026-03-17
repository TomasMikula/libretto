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
    decodeTNamed("Forall_apply")[F :: TNil](
      [⋅⋅[_]] => k ?=> [F0[_ <: ⋅⋅[K]]] =>
        () =>
          (f: [A <: ⋅⋅[K]] => Unit => F0[A]) =>
            k.splice(Box.pack[Code[K], F :: TNil])[
              ([A <: ⋅⋅[K]] => Unit => F0[A]) => Box[Code[K], F :: TNil]
            ](f): Forall[K, F]
    )

  extension [K, F <: AnyKind](f: Forall[K, F])
    transparent inline def at: Any =
      Box.unpack(f)
}
