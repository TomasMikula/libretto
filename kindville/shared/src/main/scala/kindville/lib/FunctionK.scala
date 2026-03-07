package kindville.lib

import kindville.*

class FunctionK[K, F <: AnyKind, G <: AnyKind](
  value: Box[FunctionK.Code[K], F :: G :: TNil]
) {
  transparent inline def apply(using inline di: DummyImplicit) =
    Box.unpack(value)

  transparent inline infix def andThen[H <: AnyKind](that: FunctionK[K, G, H]): Any =
    decodeExprNamed("FunctionK_andThen")[F :: G :: H :: TNil](
      [⋅⋅[_]] => k ?=> [F0[_], G0[_], H0[_]] => () =>
        val make: ([A <: ⋅⋅[K]] => F0[A] => H0[A]) => FunctionK[K, F, H] =
          k.disguise(FunctionK[K, F, H])
        val f0: [A <: ⋅⋅[K]] => F0[A] => G0[A] =
          k.disguise(this.apply)
        val g0: [A <: ⋅⋅[K]] => G0[A] => H0[A] =
          k.disguise(that.apply)[[A <: ⋅⋅[K]] => G0[A] => H0[A]]
        make([A <: ⋅⋅[K]] => (fa: F0[A]) => g0(f0(fa)))
    )()

  transparent inline infix def after[E <: AnyKind](that: FunctionK[K, E, F]): Any =
    that andThen this
}

object FunctionK {
  private[FunctionK] type Code[K] =
    [⋅⋅[_]] =>> [F0[_], G0[_]] =>>
      [A <: ⋅⋅[K]] => F0[A] => G0[A]

  transparent inline def apply[K, F <: AnyKind, G <: AnyKind] =
    decodeExprNamed("FunctionK_apply")[F :: G :: TNil](
      [⋅⋅[_]] => k ?=> [F0[_ <: ⋅⋅[K]], G0[_ <: ⋅⋅[K]]] => () =>
        (f: [A <: ⋅⋅[K]] => F0[A] => G0[A]) =>
          new FunctionK[K, F, G](
            k.disguise(Box.pack[Code[K], F :: G :: TNil])[
              ([A <: ⋅⋅[K]] => F0[A] => G0[A]) => Box[Code[K], F :: G :: TNil]
            ](f)
          )
    )()

  transparent inline def make[K] =
    decodeExprNamed0("FunctionK_mk")(
      [⋅⋅[_]] => (k: Kuotes[⋅⋅]) ?=> () =>
        [F[_ <: ⋅⋅[K]], G[_ <: ⋅⋅[K]]] =>
          (f: [A <: ⋅⋅[K]] => F[A] => G[A]) =>
            new FunctionK[K, F, G](
              k.disguise(Box.packer[Code[K]])[
                [F[_ <: ⋅⋅[K]], G[_ <: ⋅⋅[K]]] => ([A <: ⋅⋅[K]] => F[A] => G[A]) => Box[Code[K], F :: G :: TNil]
              ]
                .apply[F, G](f)
            )
    )()
}
