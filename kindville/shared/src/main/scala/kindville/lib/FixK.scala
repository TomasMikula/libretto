package kindville.lib

import kindville.{`*`, ::, ->, KindExpand, TypeApp, ofKind, ofKinds}

trait FixK[F <: AnyKind, As] {
  type Ks
  type FF <: AnyKind
  type FFFAs

  val ev1: As ofKinds Ks
  val ev2: KindExpand[Ks, FixK[F, _], FF]
  val ev3: TypeApp[F, FF :: As, FFFAs]

  def ev4: FF ofKind (Ks -> *)
  def ev5: F ofKind (((Ks -> *) :: Ks) -> *)
}
