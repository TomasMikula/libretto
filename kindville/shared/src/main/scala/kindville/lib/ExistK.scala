package kindville.lib

import kindville.{::, Box, TNil, decodeTNamed}
import kindville.Kuotes.*

opaque type ExistK[K, F <: AnyKind] =
  Box[ExistK.Code[K], F :: TNil]

object ExistK {
  private[lib] type Code[K] =
    [⋅⋅[_]] =>> [F0[_ <: ⋅⋅[K]]] =>>
      [R] => ([A <: ⋅⋅[K]] => F0[A] => R) => R

  /** Returns `[A, ...] => F[A, ...] => ExistK[K, F]`. */
  transparent inline def apply[K, F <: AnyKind] =
    decodeTNamed("ExistK_apply")[F :: TNil](
      [⋅⋅[_]] => kuotes ?=> [F0[_ <: ⋅⋅[K]]] =>
        () =>
          val pack: ([R] => ([A <: ⋅⋅[K]] => F0[A] => R) => R) => Box[Code[K], F0 :: TNil] =
            kuotes.splice(Box.pack[Code[K], F :: TNil])
          [A <: ⋅⋅[K]] => (fa: F0[A]) =>
            pack(
              [R] => (f: [X <: ⋅⋅[K]] => F0[X] => R) => f[A](fa)
            ) : ExistK[K, F0]
    )


  def types[As]: ExistsTypes[As] =
    new ExistsTypes[As]

  final class ExistsTypes[As] {
    transparent inline def suchThat[K, F <: AnyKind]: Any =
      decodeTNamed("ExistK_suchThat")[F :: As :: TNil](
        [⋅⋅[_]] => kuotes ?=> [F0[_ <: ⋅⋅[K]], A <: ⋅⋅[K]] => () =>
          val create: [X <: ⋅⋅[K]] => F0[X] => ExistK[K, F] =
            kuotes.splice(apply[K, F])
          create[A]
      )
  }

  extension [K, F <: AnyKind](ex: ExistK[K, F])
    /** Returns `[R] => ([A, ...] => F[A, ...] => R) => R`. */
    transparent inline def visit: Any =
      Box.unpack(ex)

}
