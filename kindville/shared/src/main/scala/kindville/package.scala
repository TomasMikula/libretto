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

  // TODO: provide macro-generated evidence for arbitrary kinds
}

infix sealed trait ofKinds[As, Ks] {

  /** Allows kind-polymorphic manipulation of terms involving types `As`, without static knowledge of `As`;
   * static knowledge of `Ks` is still necessary.
   */
  inline def decode[R](
    inline f: [⋅⋅[_]] => () => [A0s <: ⋅⋅[Ks]] => (⋅⋅[A0s] =~= As) => R,
  ): R =
    ${ ofKinds.decodeImpl[Ks, As, R]('{this}, 'f) }

}

object ofKinds {

  def decodeImpl[Ks, As, R](
    witness: Expr[As ofKinds Ks],
    f: Expr[[⋅⋅[_]] => () => [A0s <: ⋅⋅[Ks]] => (⋅⋅[A0s] =~= As) => R],
  )(using Quotes, Type[Ks], Type[As], Type[R]): Expr[R] =
    insideMacroExpansion:
      new Encoding().decode(witness, f)

  given [A, K] => (A ofKind K) => (A ofKinds K) =
    new (A ofKinds K) {}

  given (TNil ofKinds TNil) =
    new (TNil ofKinds TNil) {}

  given [A0, As, K0, Ks] => (A0 ofKind K0, As ofKinds Ks) => ((A0 :: As) ofKinds (K0 :: Ks)) =
    new ((A0 :: As) ofKinds (K0 :: Ks)) {}

}

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
