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
    // basically just `Box.pack`, but need the result to return Action instead of Box
    decodeT[G :: F :: TNil](
      [⋅⋅[_]] => (k: Kuotes[⋅⋅]) ?=> [G0[_ <: ⋅⋅[K]], F0[_ <: ⋅⋅[K], _ <: ⋅⋅[K]]] => () =>
        val pack: ([X <: ⋅⋅[K], Y <: ⋅⋅[K]] => (G0[X], F0[X, Y]) => G0[Y]) => Action[K, G, F] =
          k.splice(Box.pack[Code[K], G :: F :: TNil])
        pack
    )

  extension [K, G <: AnyKind, F <: AnyKind](a: Action[K, G, F]) {
    /** Returns `[X, Y] => (G[X], F[X, Y]) => G[Y]`. */
    transparent inline def unpack =
      Box.unpack[Code[K], G :: F :: TNil](a)
  }

  extension [K, G <: AnyKind, F <: AnyKind](a: Action[K, G, F]) {
    /** Returns `[A, B] => (G[A], F[A, B]) => G[B]` */
    transparent inline def act =
      unpack[K, G, F](a)

    /** Returns `[A, B] => (by: F[A, B]) => (on: G[A]) => G[B]` */
    transparent inline def actBy =
      decodeT[G :: F :: TNil](
        [⋅⋅[_]] => k ?=> [G0[_ <: ⋅⋅[K]], F0[_ <: ⋅⋅[K], _ <: ⋅⋅[K]]] => () =>
          [A <: ⋅⋅[K], B <: ⋅⋅[K]] => (f: F0[A, B]) => (on: G0[A]) =>
            k.splice(a.act)[[A <: ⋅⋅[K], B <: ⋅⋅[K]] => (G0[A], F0[A, B]) => G0[B]][A, B](on, f)
      )

    /** Returns `[A, B] => (on: G[A]) => (by: F[A, B]) => G[B]` */
    transparent inline def actOn =
      decodeT[G :: F :: TNil](
        [⋅⋅[_]] => k ?=> [G0[_ <: ⋅⋅[K]], F0[_ <: ⋅⋅[K], _ <: ⋅⋅[K]]] => () =>
          [A <: ⋅⋅[K], B <: ⋅⋅[K]] => (on: G0[A]) => (f: F0[A, B]) =>
            k.splice(a.act)[[A <: ⋅⋅[K], B <: ⋅⋅[K]] => (G0[A], F0[A, B]) => G0[B]][A, B](on, f)
      )

    transparent inline def apply[A <: AnyKind, B <: AnyKind](
      ga: App[K, G, A],
      f: Arrow[K, F, A, B],
    ): App[K, G, B] =
      decodeT[G :: F :: A :: B :: TNil](
        [⋅⋅[_]] => k ?=> [G0[_ <: ⋅⋅[K]], F0[_ <: ⋅⋅[K], _ <: ⋅⋅[K]], A0 <: ⋅⋅[K], B0 <: ⋅⋅[K]] => () =>
          val x: G0[A0] =
            k.splice(App.unpack(ga))
          val h: F0[A0, B0] =
            k.splice(Arrow.unpack(f))
          val y: G0[B0] =
            k.splice(a.act)[[A <: ⋅⋅[K], B <: ⋅⋅[K]] => (G0[A], F0[A, B]) => G0[B]][A0, B0](x, h)
          k.splice(App.pack[K, G, B])[G0[B0] => App[K, G, B]](y)
      )
        .typecheckAs[App[K, G, B]]
  }
}
