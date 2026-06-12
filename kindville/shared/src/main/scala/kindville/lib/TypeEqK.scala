package kindville.lib

import kindville.*

class TypeEqK[K, F <: AnyKind, G <: AnyKind](
  val value: Box[TypeEqK.Code[K], F :: G :: TNil] // TODO: make private
) {
  transparent inline def substituteCo =
    Box.unpack[TypeEqK.Code[K], F :: G :: TNil](value)

  inline def substituteCoApp[H <: AnyKind](hf: App[K, H, F]): App[K, H, G] =
    decodeT[F :: G :: H :: TNil](
      [⋅⋅[_]] => kuotes ?=> [F <: ⋅⋅[K], G <: ⋅⋅[K], H[_ <: ⋅⋅[K]]] => () =>
        val x: App[K, H, ⋅⋅[F]] =
          kuotes.splice(hf)
        val subst: [M[X <: ⋅⋅[K]]] => M[F] => M[G] =
          kuotes.splice(this.substituteCo)
        subst[[X <: ⋅⋅[K]] =>> App[K, H, ⋅⋅[X]]](x)
    )
      .typecheckAs[App[K, H, G]]

  inline def substituteCoAppDynamic[H <: AnyKind](hf: App[K, H, F])(using
    evf: F ofKinds K,
    evg: G ofKinds K,
    evh: H ofKinds (K -> *),
  ): App[K, H, G] =
    evf.decode:
      [⋅[_]] => () => [F0 <: ⋅[K]] => (evf: ⋅[F0] =~= F) =>
        evg.decode:
          [⋅⋅[_]] => () => [G0 <: ⋅⋅[K]] => (evg: ⋅⋅[G0] =~= G) =>
            evh.decode:
              [⋅⋅⋅[_]] => () => [H0 <: ⋅⋅⋅[K -> *]] => (evh: ⋅⋅⋅[H0] =~= H) =>
                val hf0: App[K, ⋅⋅⋅[H0], ⋅[F0]] = evh.substituteContra[[h <: AnyKind] =>> App[K, h, ⋅[F0]]](evf.substituteContra(hf))
                val self: TypeEqK[K, ⋅[F0], ⋅⋅[G0]] = evf.substituteContra[[f <: AnyKind] =>> TypeEqK[K, f, ⋅⋅[G0]]](evg.substituteContra(this))
                val res: App[K, ⋅⋅⋅[H0], ⋅⋅[G0]] = self.substituteCoApp[⋅⋅⋅[H0]](hf0)
                evh.substituteCo[[h <: AnyKind] =>> App[K, h, G]](evg.substituteCo(res))

  transparent inline def andThen[H <: AnyKind](that: TypeEqK[K, G, H]) =
    decodeT[F :: G :: H :: TNil](
      [⋅⋅[_]] => kuotes ?=> [F <: ⋅⋅[K], G <: ⋅⋅[K], H <: ⋅⋅[K]] => () =>
        val thiz: TypeEqK[K, ⋅⋅[F], ⋅⋅[G]] =
          kuotes.splice(this)
        val subst: [M[X <: ⋅⋅[K]]] => M[G] => M[H] =
          kuotes.splice(that.substituteCo)
        subst[[J <: ⋅⋅[K]] =>> TypeEqK[K, ⋅⋅[F], ⋅⋅[J]]](thiz)
    )

  transparent inline def flip =
    decodeT[F :: G :: TNil](
      [⋅⋅[_]] => (k: Kuotes[⋅⋅]) ?=> [F <: ⋅⋅[K], G <: ⋅⋅[K]] => () =>
        val refl: [H <: ⋅⋅[K]] => () => TypeEqK[K, ⋅⋅[H], ⋅⋅[H]] =
          k.splice(TypeEqK.refl[K])
        val subst: [M[X <: ⋅⋅[K]]] => M[F] => M[G] =
          k.splice(this.substituteCo)
        subst[[J <: ⋅⋅[K]] =>> TypeEqK[K, ⋅⋅[J], ⋅⋅[F]]](refl[F]())
    )
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

  transparent inline def refl[K] =
    decode(
      [⋅⋅[_]] => (k: Kuotes[⋅⋅]) ?=>
        val packer: [F <: ⋅⋅[K], G <: ⋅⋅[K]] => ([H[_ <: ⋅⋅[K]]] => H[F] => H[G]) => Box[Code[K], ⋅⋅[F] :: ⋅⋅[G] :: TNil] =
          k.splice(Box.packer[Code[K]])
        [F <: ⋅⋅[K]] => () =>
          Refl[K, ⋅⋅[F]]()(
            packer[F, F](
              [H[_ <: ⋅⋅[K]]] => (hf: H[F]) => hf
            )
          )
    )
}
