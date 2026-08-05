package kindville

import kindville.Reporting.{inside, insideMacroExpansion}
import scala.quoted.*

private transparent inline def qr(using Quotes): quotes.reflect.type =
  quotes.reflect

inline def compiletimeKindCheck[A <: AnyKind, K]: Unit =
  ${ compiletimeKindCheckImpl[A, K] }

private def compiletimeKindCheckImpl[A <: AnyKind, K](using Type[A], Type[K], Quotes): Expr[Unit] =
  insideMacroExpansion:
    new Encoding().compiletimeKindCheck[A, K]

transparent inline def decode(inline expr: [⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any): Any =
  ${ decodeImpl('expr) }

transparent inline def decodeT[As](
  inline expr: [⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any,
  inline considering: (? ofKinds ?)*,
): Any =
  ${ decodeTImpl[As]('expr, 'considering) }

private def decodeImpl(expr: Expr[[⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any])(using Quotes): Expr[Any] =
  insideMacroExpansion:
    import quotes.reflect.*
    val encoding = Encoding()
    encoding
      .decodeExpr(expr)

private def decodeTImpl[As](
  expr: Expr[[⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any],
  considering: Expr[Seq[? ofKinds ?]],
)(using
  Quotes,
  Type[As],
): Expr[Any] =
  insideMacroExpansion:
    import quotes.reflect.*

    considering match
      case Varargs(considerings) =>
        val encoding = Encoding()
        encoding
          .decodeExprT[As](expr, considerings)
      case _ =>
        report.errorAndAbort("Expected explicit varargs sequence.", considering)

extension [A](inline a: A)
  inline def typecheckAs[B]: B =
    ${ typecheckAsImpl[A, B]('a) }

private def typecheckAsImpl[A, B](a: Expr[A])(using Quotes, Type[B]): Expr[B] =
  a.asExprOf[B]
