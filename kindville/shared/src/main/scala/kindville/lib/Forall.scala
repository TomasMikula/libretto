package kindville.lib

import kindville.*

// TODO: use an opaque type alias when
// https://github.com/scala/scala3/issues/13461#issuecomment-2002566051
// is resolved.
// TODO: Perhaps in the meantime, place the opaque type alias to a separate file.
class Forall[K, F <: AnyKind](
  private[Forall] val value: Box[Forall.Code[K], F :: TNil]
)

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
            new Forall[K, F](
              pack(f)
            )
    )(
      Box.pacK[(K ->> *) :: TNil, Code[K], F :: TNil]
    )

  extension [K, F <: AnyKind](f: Forall[K, F])
    transparent inline def at: Any =
      Box.unpack(f.value)
}
