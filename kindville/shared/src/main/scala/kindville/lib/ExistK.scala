package kindville.lib

import kindville.{::, Box, TNil, decodeExpr}

opaque type ExistK[K, F <: AnyKind] =
  Box[ExistK.Code[K], F :: TNil]

object ExistK {
  private[lib] type Code[K] =
    [⋅⋅[_]] =>> [F0[_ <: ⋅⋅[K]]] =>>
      [R] => ([A <: ⋅⋅[K]] => F0[A] => R) => R

  /** Returns `[A, ...] => F[A, ...] => ExistK[K, F]`. */
  transparent inline def apply[K, F <: AnyKind] =
    decodeExpr[F :: TNil](
      [⋅⋅[_], F0[_ <: ⋅⋅[K]]] =>
        (pack: ([R] => ([A <: ⋅⋅[K]] => F0[A] => R) => R) => Box[Code[K], F :: TNil]) =>
          [A <: ⋅⋅[K]] => (fa: F0[A]) =>
            pack(
              [R] => (f: [X <: ⋅⋅[K]] => F0[X] => R) => f[A](fa)
            ): ExistK[K, F]
    )(Box.pack[Code[K], F :: TNil])



  def types[As]: ExistsTypes[As] =
    new ExistsTypes[As]

  final class ExistsTypes[As] {
    transparent inline def suchThat[K, F <: AnyKind]: Any =
      decodeExpr[F :: As :: TNil](
        [⋅⋅[_], F0[_ <: ⋅⋅[K]], A <: ⋅⋅[K]] =>
          (create: [X <: ⋅⋅[K]] => F0[X] => ExistK[K, F]) =>
            create[A]
      )(apply[K, F])
  }

  extension [K, F <: AnyKind](ex: ExistK[K, F])
    /** Returns `[R] => ([A, ...] => F[A, ...] => R) => R`. */
    transparent inline def visit: Any =
      Box.unpack(ex)

}
