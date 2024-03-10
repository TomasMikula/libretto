package kindville.lib

import kindville.{::, Box, TNil, decodeExpr}

opaque type ExistK[K, F <: AnyKind] =
  Box[
    F :: TNil,
    ExistK.Code[K],
  ]

object ExistK {
  private[lib] type Code[K] =
    [⋅⋅[_]] =>> [F0[_]] =>>
      [R] => ([A <: ⋅⋅[K]] => F0[A] => R) => R

  /** Returns `[A, ...] => F[A, ...] => ExistK[K, F]`. */
  transparent inline def apply[K, F <: AnyKind] =
    decodeExpr[F :: TNil](
      [⋅⋅[_], F0[_]] => (_: Unit) =>
        [A <: ⋅⋅[K]] => (fa: F0[A]) =>
          [R] => (f: [X <: ⋅⋅[K]] => F0[X] => R) => f[A](fa)
    )

  extension [K, F <: AnyKind](e: ExistK[K, F])
    /** Returns `[R] => ([A, ...] => F[A, ...] => R) => R`. */
    transparent inline def visit: Any =
      Box.unpack(e)
}
