package kindville

import kindville.Encoding.*
import scala.quoted.*

sealed trait TypeApp[F <: AnyKind, +As, FAs]

object TypeApp {
  private case class MacroCertified[F <: AnyKind, As, FAs]() extends TypeApp[F, As, FAs]

  transparent inline def inferResult[F <: AnyKind, As]: TypeApp[F, As, ?] =
    ${ inferResultImpl[F, As] }

  transparent inline def inferArgs[F <: AnyKind, FAs]: TypeApp[F, ?, FAs] =
    ${ inferArgsImpl[F, FAs] }

  def functional[F <: AnyKind, As, FA1, FA2](
    a1: TypeApp[F, As, FA1],
    a2: TypeApp[F, As, FA2],
  ): FA1 =:= FA2 =
    summon[FA1 =:= FA1]
      .asInstanceOf[FA1 =:= FA2]

  private[kindville] def inferResultImpl[F <: AnyKind, As](using
    Quotes,
    Type[F],
    Type[As],
  ): Expr[TypeApp[F, As, ?]] = {
    import quotes.reflect.*

    type FAs
    given Type[FAs] =
      TypeRepr.of[F]
        .appliedTo(decodeTypeArgs(Type.of[As]).map(TypeRepr.of(using _)))
        .asType
        .asInstanceOf[Type[FAs]]
    val resultType =
      TypeRepr
        .of[TypeApp]
        .appliedTo(List(TypeRepr.of[F], TypeRepr.of[As], TypeRepr.of[FAs]))
        .asType
        .asInstanceOf[Type[TypeApp[F, As, FAs]]]
    // '{ MacroCertified[F, As, FAs]() }.asExprOf(using resultType)
    Typed(
      '{ MacroCertified[F, As, FAs]() }.asTerm,
      TypeTree.of(using resultType),
    ).asExprOf(using resultType)
  }

  private[kindville] def inferArgsImpl[F <: AnyKind, FAs](using
    Quotes,
    Type[F],
    Type[FAs],
  ): Expr[TypeApp[F, ?, FAs]] =
    import quotes.reflect.*

    val fRepr   = TypeRepr.of[F]
    val fasRepr = TypeRepr.of[FAs]

    fasRepr match
      case AppliedType(f, args) if f =:= fRepr =>
        val as: TypeRepr = encodeTypeArgs(args)
        val resultType =
          TypeRepr
            .of[TypeApp]
            .appliedTo(List(fRepr, as, fasRepr))
            .asType
            .asInstanceOf[Type[TypeApp[F, ?, FAs]]]
        '{ MacroCertified[F, Nothing, FAs]() }.asExprOf(using resultType)
      case f if f =:= fRepr =>
        // F = FAs (i.e. F does not take type parameters)
        '{ MacroCertified[F, TNil, FAs]() }
      case other =>
        val fStr   = Printer.TypeReprCode.show(fRepr)
        val fasStr = Printer.TypeReprCode.show(fasRepr)
        val msg = s"Expected ${fStr} applied to some type arguments, got ${fasStr}"
        report.error(msg)
        '{ ??? }
}
