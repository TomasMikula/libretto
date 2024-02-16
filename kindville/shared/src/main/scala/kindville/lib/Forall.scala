package kindville.lib

import kindville.TypeApp

trait Forall[F <: AnyKind] {
  def ats[As, FAs](using TypeApp[F, As, FAs]): FAs
}
