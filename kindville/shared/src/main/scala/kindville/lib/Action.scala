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

    inline def apply[A <: AnyKind, B <: AnyKind](
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

    inline def applyOpt[A <: AnyKind, B <: AnyKind](
      ga: App[K, G, A],
      fOpt: Arrow.Opt[K, F, A, B],
    ): App[K, G, B] =
      fOpt match
        case Arrow.Opt.Some(f) =>
          apply(ga, f)
        case Arrow.Opt.None() =>
          ga

    /** Like [[apply]], but `A` and `B` don't need to be statically known. Instead, this method takes trusted evidence of `A`'s and `B`'s kindedness.
     *
     * Note that [[K]], [[G]], [[F]] still need to be statically known).
     */
    inline def applyDynamic[A <: AnyKind, B <: AnyKind](
      ga: App[K, G, A],
      f: Arrow[K, F, A, B],
    )(using
      A: (A ofKinds K),
      B: (B ofKinds K),
    ): App[K, G, B] =
      A.decode[App[K, G, B]]:
        [⋅⋅[_]] => () => [A0 <: ⋅⋅[K]] => (eva: ⋅⋅[A0] =~= A) ?=>
          B.decode[App[K, G, B]]:
            [⋅⋅⋅[_]] => () => [B0 <: ⋅⋅⋅[K]] => (evb: ⋅⋅⋅[B0] =~= B) ?=>
              val ga0: App[K, G, ⋅⋅[A0]] = eva.substituteContra(ga)
              val f0: Arrow[K, F, ⋅⋅[A0], ⋅⋅⋅[B0]] = eva.substituteContra[[X <: AnyKind] =>> Arrow[K, F, X, ⋅⋅⋅[B0]]](evb.substituteContra(f))
              val gb0: App[K, G, ⋅⋅⋅[B0]] = apply[⋅⋅[A0], ⋅⋅⋅[B0]](ga0, f0)
              evb.substituteCo(gb0)

  }
}
