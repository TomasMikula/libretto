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
  ${ decodeImpl('expr) }

transparent inline def decodeT[As](inline expr: [⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any): Any =
  decodeFull[[⋅⋅[_]] =>> As](expr)

transparent inline def decodeFull[As[⋅⋅[_]]](inline expr: [⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any): Any =
  ${ decodeFullImpl[As]('expr) }

private def decodeImpl(expr: Expr[[⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any])(using Quotes): Expr[Any] =
  insideMacroExpansion:
    import quotes.reflect.*
    val encoding = Encoding()
    encoding
      .decodeExpr(expr)

private def decodeFullImpl[As[⋅⋅[_]]](expr: Expr[[⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any])(using Quotes, Type[As]): Expr[Any] =
  insideMacroExpansion:
    import quotes.reflect.*
    val encoding = Encoding()
    encoding
      .decodeExprT[As](expr)

extension [A](inline a: A)
  inline def typecheckAs[B]: B =
    ${ typecheckAsImpl[A, B]('a) }

private def typecheckAsImpl[A, B](a: Expr[A])(using Quotes, Type[B]): Expr[B] =
  a.asExprOf[B]
