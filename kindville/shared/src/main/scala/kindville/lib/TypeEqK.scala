package kindville.lib

import kindville.*

class TypeEqK[K, F <: AnyKind, G <: AnyKind](
  value: Box[TypeEqK.Code[K], F :: G :: TNil]
) {
  transparent inline def substituteCo =
    Box.unpack[TypeEqK.Code[K], F :: G :: TNil](value)

  transparent inline def andThen[H <: AnyKind](that: TypeEqK[K, G, H]) =
    decodeExpr[F :: G :: H :: TNil](
      [⋅⋅[_], F <: ⋅⋅[K], G <: ⋅⋅[K], H <: ⋅⋅[K]] => (
        thiz: TypeEqK[K, F, G],
        subst: [M[X <: ⋅⋅[K]]] => M[G] => M[H]
      ) =>
        subst[[J <: ⋅⋅[K]] =>> TypeEqK[K, F, J]](thiz)
    )(
      this,
      that.substituteCo
    )

  transparent inline def flip =
    decodeExpr[F :: G :: TNil](
      [⋅⋅[_], F <: ⋅⋅[K], G <: ⋅⋅[K]] => (
        refl: [H <: ⋅⋅[K]] => Unit => TypeEqK[K, H, H],
        subst: [M[X <: ⋅⋅[K]]] => M[F] => M[G]
      ) =>
        subst[[J <: ⋅⋅[K]] =>> TypeEqK[K, J, F]](refl[F](()))
    )(
      TypeEqK.refl[K],
      this.substituteCo
    )
}

object TypeEqK {

  /** Represent the equality of `F` and `G` as `∀H. H[F] => H[G]`,
   *  analogous to the [[=:=.substituteCo]] method.
   */
  type Code[K] = [⋅⋅[_]] =>>
    [F <: ⋅⋅[K], G <: ⋅⋅[K]] =>>
      [H[X <: ⋅⋅[K]]] => H[F] => H[G]

  transparent inline def refl[K]: Any =
    decodeExpr[TNil](
      [⋅⋅[_]] =>
        (packer: [F <: ⋅⋅[K], G <: ⋅⋅[K]] => ([H[_ <: ⋅⋅[K]]] => H[F] => H[G]) => Box[Code[K], F :: G :: TNil]) =>
          [F <: ⋅⋅[K]] => (_: Unit) =>
            new TypeEqK[K, F, F](
              packer[F, F](
                [H[_ <: ⋅⋅[K]]] => (hf: H[F]) => hf
              )
            )
    )(
      Box.packer[Code[K]]
    )
}
