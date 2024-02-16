package kindville.lib

import kindville.TypeApp

sealed trait Exists[F <: AnyKind] {
  type Args
  type Res
  def ev: TypeApp[F, Args, Res]
  def value: Res
}

object Exists {
  case class Some[F <: AnyKind, As, FAs](
    ev: TypeApp[F, As, FAs],
    value: FAs,
  ) extends Exists[F] {
    override type Args = As
    override type Res = FAs
  }

  def apply[F <: AnyKind, As, FAs](fa: FAs)(using TypeApp[F, As, FAs]): Exists[F] =
    Some(summon[TypeApp[F, As, FAs]], fa)
}
