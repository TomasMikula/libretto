package kindville.lib

import kindville.*

class FunctionK[K, F <: AnyKind, G <: AnyKind](
  value: Box[FunctionK.Code[K], F :: G :: TNil]
) {
  transparent inline def apply(using inline di: DummyImplicit) =
    Box.unpack(value)

  transparent inline infix def andThen[H <: AnyKind](that: FunctionK[K, G, H]): Any =
    decodeExpr[F :: G :: H :: TNil](
      [⋅⋅[_], F0[_], G0[_], H0[_]] => (
        make: ([A <: ⋅⋅[K]] => F0[A] => H0[A]) => FunctionK[K, F, H],
        f0: [A <: ⋅⋅[K]] => F0[A] => G0[A],
        g0: [A <: ⋅⋅[K]] => G0[A] => H0[A]
      ) =>
        make([A <: ⋅⋅[K]] => (fa: F0[A]) => g0(f0(fa)))
    )(
      FunctionK[K, F, H],
      this.apply,
      that.apply,
    )

  transparent inline infix def after[E <: AnyKind](that: FunctionK[K, E, F]): Any =
    that andThen this
}

object FunctionK {
  private[FunctionK] type Code[K] =
    [⋅⋅[_]] =>> [F0[_], G0[_]] =>>
      [A <: ⋅⋅[K]] => F0[A] => G0[A]

  transparent inline def apply[K, F <: AnyKind, G <: AnyKind] =
    make[K]
      .polyFunAt[F :: G :: TNil]

  transparent inline def make[K] =
    decodeFun(
      [⋅⋅[_], F[_ <: ⋅⋅[K]], G[_ <: ⋅⋅[K]]] =>
        (f: [A <: ⋅⋅[K]] => F[A] => G[A]) =>
          new FunctionK[K, F, G](
            Box.packer[Code[K]]
              .polyFunApply[
                F :: G :: TNil,
                Box[Code[K], F :: G :: TNil]
              ](f)
          )
    )
}
