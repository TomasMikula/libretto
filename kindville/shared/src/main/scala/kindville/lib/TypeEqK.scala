package kindville.lib

import kindville.*

class TypeEqK[K, F <: AnyKind, G <: AnyKind](
  value: Box[TypeEqK.Code[K], F :: G :: TNil]
) {
  transparent inline def substituteCo =
    Box.unpack[TypeEqK.Code[K], F :: G :: TNil](value)
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
