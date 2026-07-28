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

object ofKind {

  given [A] => (A ofKind *) =
    new (A ofKind *) {}

  given [F[_]] => (F ofKind (* -> *)) =
    new (F ofKind (* -> *)) {}

  given [F2[_, _]] => (F2 ofKind ((* :: * :: TNil) -> *)) =
    new (F2 ofKind ((* :: * :: TNil) -> *)) {}

  given [H[_[_]]] => (H ofKind ((* -> *) -> *)) =
    new (H ofKind ((* -> *) -> *)) {}

  // TODO: provide macro-generated evidence for arbitrary kinds
}

infix sealed trait ofKinds[As <: AnyKind, Ks]

object ofKinds {

  given [A <: AnyKind, K] => (A ofKind K) => (A ofKinds K) =
    new (A ofKinds K) {}

  given (TNil ofKinds TNil) =
    new (TNil ofKinds TNil) {}

  given [A0, As, K0, Ks] => (A0 ofKind K0, As ofKinds Ks) => ((A0 :: As) ofKinds (K0 :: Ks)) =
    new ((A0 :: As) ofKinds (K0 :: Ks)) {}

}

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
  decodeFull[[⋅⋅[_]] =>> As](expr, considering*)

transparent inline def decodeFull[As[⋅⋅[_]]](
  inline expr: [⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any,
  inline considering: (? ofKinds ?)*,
): Any =
  ${ decodeFullImpl[As]('expr, 'considering) }

private def decodeImpl(expr: Expr[[⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any])(using Quotes): Expr[Any] =
  insideMacroExpansion:
    import quotes.reflect.*
    val encoding = Encoding()
    encoding
      .decodeExpr(expr)

private def decodeFullImpl[As[⋅⋅[_]]](
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
