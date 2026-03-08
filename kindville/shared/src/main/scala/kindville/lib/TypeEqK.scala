package kindville.lib

import kindville.*

class TypeEqK[K, F <: AnyKind, G <: AnyKind](
  value: Box[TypeEqK.Code[K], F :: G :: TNil]
) {
  transparent inline def substituteCo =
    Box.unpack[TypeEqK.Code[K], F :: G :: TNil](value)

  transparent inline def andThen[H <: AnyKind](that: TypeEqK[K, G, H]) =
    decodeTNamed("TypeEqK_andThen")[F :: G :: H :: TNil](
      [⋅⋅[_]] => kuotes ?=> [F <: ⋅⋅[K], G <: ⋅⋅[K], H <: ⋅⋅[K]] => () =>
        val thiz: TypeEqK[K, F, G] =
          kuotes.splice(this)
        val subst: [M[X <: ⋅⋅[K]]] => M[G] => M[H] =
          kuotes.splice(that.substituteCo)
        subst[[J <: ⋅⋅[K]] =>> TypeEqK[K, F, J]](thiz)
    )()

  transparent inline def flip =
    decodeTNamed("TypeEqK_flip")[F :: G :: TNil](
      [⋅⋅[_]] => (k: Kuotes[⋅⋅]) ?=> [F <: ⋅⋅[K], G <: ⋅⋅[K]] => () =>
        val refl: [H <: ⋅⋅[K]] => () => TypeEqK[K, H, H] =
          k.splice(TypeEqK.refl[K])
        val subst: [M[X <: ⋅⋅[K]]] => M[F] => M[G] =
          k.splice(this.substituteCo)
        subst[[J <: ⋅⋅[K]] =>> TypeEqK[K, J, F]](refl[F]())
    )()
}

object TypeEqK {

  /** Represent the equality of `F` and `G` as `∀H. H[F] => H[G]`,
   *  analogous to the [[=:=.substituteCo]] method.
   */
  type Code[K] = [⋅⋅[_]] =>>
    [F <: ⋅⋅[K], G <: ⋅⋅[K]] =>>
      [H[X <: ⋅⋅[K]]] => H[F] => H[G]

  case class Refl[K, F <: AnyKind]()(
    subst: Box[TypeEqK.Code[K], F :: F :: TNil]
  ) extends TypeEqK[K, F, F](subst)

  transparent inline def refl[K]: Any =
    decodeNamed("TypeEqK_refl")(
      [⋅⋅[_]] => (k: Kuotes[⋅⋅]) ?=> () =>
        val packer: [F <: ⋅⋅[K], G <: ⋅⋅[K]] => ([H[_ <: ⋅⋅[K]]] => H[F] => H[G]) => Box[Code[K], F :: G :: TNil] =
          k.splice(Box.packer[Code[K]])
        [F <: ⋅⋅[K]] => () =>
          Refl[K, F]()(
            packer[F, F](
              [H[_ <: ⋅⋅[K]]] => (hf: H[F]) => hf
            )
          )
    )()
}
