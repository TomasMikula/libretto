package kindville

import kindville.Reporting.{inside, insideMacroExpansion}
import scala.quoted.*
import scala.PolyFunction
import scala.annotation.experimental

sealed trait *
sealed trait ->>[K, L]
type ->[K, L] = (K :: TNil) ->> L

sealed trait ::[H <: AnyKind, T]
sealed trait TNil

infix sealed trait ofKind[F <: AnyKind, K]
infix sealed trait ofKinds[As, Ks]

private transparent inline def qr(using Quotes): quotes.reflect.type =
  quotes.reflect

transparent inline def decode(inline expr: [⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any): Any =
  ${ decodeNamedImpl('{""}, 'expr) }

transparent inline def decodeT[As](inline expr: [⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any): Any =
  decodeFull(nameHint = "")[[⋅⋅[_]] =>> As](expr)

transparent inline def decodeNamed(nameHint: String)(inline expr: [⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any): Any =
  ${ decodeNamedImpl('nameHint, 'expr) }

transparent inline def decodeTNamed(nameHint: String)[As](inline expr: [⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any): Any =
  decodeFull(nameHint)[[⋅⋅[_]] =>> As](expr)

transparent inline def decodeFull(nameHint: String)[As[⋅⋅[_]]](inline expr: [⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any): Any =
  ${ decodeFullImpl[As]('nameHint, 'expr) }

private def decodeNamedImpl(nameHint: Expr[String], expr: Expr[[⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any])(using Quotes): Expr[Any] =
  insideMacroExpansion:
    import quotes.reflect.*
    val encoding = Encoding()
    encoding
      .decodeExpr(Some(nameHint.valueOrAbort).filter(_.nonEmpty), expr)

private def decodeFullImpl[As[⋅⋅[_]]](nameHint: Expr[String], expr: Expr[[⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any])(using Quotes, Type[As]): Expr[Any] =
  insideMacroExpansion:
    import quotes.reflect.*
    val encoding = Encoding()
    encoding
      .decodeExprT[As](Some(nameHint.valueOrAbort).filter(_.nonEmpty), expr)

extension [A](inline a: A)
  inline def typecheckAs[B]: B =
    ${ typecheckAsImpl[A, B]('a) }

private def typecheckAsImpl[A, B](a: Expr[A])(using Quotes, Type[B]): Expr[B] =
  a.asExprOf[B]
