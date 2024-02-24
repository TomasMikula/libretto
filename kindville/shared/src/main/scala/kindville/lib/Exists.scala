package kindville.lib

import kindville.{::, TNil, TypeApp, at, encoderOf, unmask, visit}
import scala.annotation.experimental
import scala.quoted.*

sealed trait Exists[F <: AnyKind] {
  type Args
  type Res
  given ev: TypeApp[F, Args, Res]
  def value: Res

  @experimental
  transparent inline def visit: Any =
    value.visit[F, Args]
}

object Exists {
  case class Some[F <: AnyKind, As, FAs](
    ev: TypeApp[F, As, FAs],
    value: FAs,
  ) extends Exists[F] {
    override type Args = As
    override type Res = FAs
  }

  def some[F <: AnyKind, As, FAs](fa: FAs)(using TypeApp[F, As, FAs]): Exists[F] =
    Some(summon[TypeApp[F, As, FAs]], fa)

  private def some_[F <: AnyKind, As, FAs](ev: TypeApp[F, As, FAs]): FAs => Exists[F] =
    Some(ev, _)

  @experimental
  transparent inline def apply[F <: AnyKind] =
    encoderOf[F, Exists[F]](
      [As, FAs] => (value: FAs, ev: TypeApp[F, As, FAs]) => some(value)(using ev)
    )

  def types[As]: ExistsTypes[As] =
    new ExistsTypes[As]

  final class ExistsTypes[As] {
    @experimental
    transparent inline def suchThat[F <: AnyKind]: Nothing => Any =
      apply[F].at[As]
  }
}
