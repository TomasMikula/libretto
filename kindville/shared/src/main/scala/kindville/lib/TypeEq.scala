package kindville.lib

import kindville.{::, TNil, TypeApp}

sealed trait TypeEq[F <: AnyKind, G <: AnyKind] {
  def substituteCo[H <: AnyKind, HF, HG](a: HF)(using
    TypeApp[H, F :: TNil, HF],
    TypeApp[H, G :: TNil, HG],
  ): HG
}

object TypeEq {
  case class Refl[F <: AnyKind]() extends TypeEq[F, F] {
    override def substituteCo[H <: AnyKind, HF, HG](a: HF)(using
      hf: TypeApp[H, F :: TNil, HF],
      hg: TypeApp[H, F :: TNil, HG],
    ): HG =
      TypeApp.functional(hf, hg)(a)
  }
}
