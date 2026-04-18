package kindville.lib

import kindville.*

/** Action of F on G. That is, applies F[X, Y] to G[X], obtaining G[Y]. */
opaque type Action[K, G <: AnyKind, F <: AnyKind] =
  Box[Action.Code[K], G :: F :: TNil]

object Action {
  type Code[K] = [⋅⋅[_]] =>> [G[_ <: ⋅⋅[K]], F[_ <: ⋅⋅[K], _ <: ⋅⋅[K]]] =>>
    [X <: ⋅⋅[K], Y <: ⋅⋅[K]] => (G[X], F[X, Y]) => G[Y]

  /** Returns `([X, Y] => (G[X], F[X, Y]) => G[Y]) => Action[K, G, F]`. */
  transparent inline def pack[K, G <: AnyKind, F <: AnyKind] =
    // basically just `Box.pack`, but need to the result to return Action instead of Box
    decodeT[G :: F :: TNil](
      [⋅⋅[_]] => (k: Kuotes[⋅⋅]) ?=> [G0[_ <: ⋅⋅[K]], F0[_ <: ⋅⋅[K], _ <: ⋅⋅[K]]] => () =>
        val pack: ([X <: ⋅⋅[K], Y <: ⋅⋅[K]] => (G0[X], F0[X, Y]) => G0[Y]) => Action[K, G, F] =
          k.splice(Box.pack[Code[K], G :: F :: TNil])
        pack
    )

  /** Returns `[X, Y] => (G[X], F[X, Y]) => G[Y]`. */
  transparent inline def unpack[K, G <: AnyKind, F <: AnyKind](a: Action[K, G, F]) =
    Box.unpack[Code[K], G :: F :: TNil](a)

  extension [K, G <: AnyKind, F <: AnyKind](a: Action[K, G, F]) {
    /** Returns `[A, B] => (G[A], F[A, B]) => G[B]` */
    transparent inline def act =
      unpack[K, G, F](a)
  }
}
