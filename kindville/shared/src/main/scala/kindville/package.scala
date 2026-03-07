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

transparent inline def decodeExpr[As](inline expr: Any)(inline args: Any*): Any =
  decodeCompositeExpr[[⋅⋅[_]] =>> As](expr)(args*)

transparent inline def decodeExpr1[As](inline expr: [⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any)(inline args: Any*): Any =
  decodeCompositeExpr1(nameHint = "")[[⋅⋅[_]] =>> As](expr)(args*)

transparent inline def decodeExprNamed0(nameHint: String)(inline expr: [⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any)(inline args: Any*): Any =
  ${ decodeExprNamed0Impl('nameHint, 'expr, 'args) }

transparent inline def decodeExprNamed(nameHint: String)[As](inline expr: [⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any)(inline args: Any*): Any =
  decodeCompositeExpr1(nameHint)[[⋅⋅[_]] =>> As](expr)(args*)

transparent inline def decodeCompositeExpr[As[⋅⋅[_]]](inline expr: Any)(inline args: Any*): Any =
  ${ decodeCompositeExprImpl[As]('expr, 'args) }

transparent inline def decodeCompositeExpr1(nameHint: String)[As[⋅⋅[_]]](inline expr: [⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any)(inline args: Any*): Any =
  ${ decodeCompositeExprImpl1[As]('nameHint, 'expr, 'args) }

private def decodeCompositeExprImpl[As[⋅⋅[_]]](expr: Expr[Any], args: Expr[Seq[Any]])(using Quotes, Type[As]): Expr[Any] =
  insideMacroExpansion:
    import quotes.reflect.*
    val encoding = Encoding()
    val as = unVarargs(args).toList
    encoding
      .decodeParameterizedTerm[As](expr, as)

private def decodeExprNamed0Impl(nameHint: Expr[String], expr: Expr[[⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any], args: Expr[Seq[Any]])(using Quotes): Expr[Any] =
  insideMacroExpansion:
    import quotes.reflect.*
    val encoding = Encoding()
    val as = unVarargs(args).toList
    encoding
      .decodeParameterizedTerm0(Some(nameHint.valueOrAbort).filter(_.nonEmpty), expr, as)

private def decodeCompositeExprImpl1[As[⋅⋅[_]]](nameHint: Expr[String], expr: Expr[[⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any], args: Expr[Seq[Any]])(using Quotes, Type[As]): Expr[Any] =
  insideMacroExpansion:
    import quotes.reflect.*
    val encoding = Encoding()
    val as = unVarargs(args).toList
    encoding
      .decodeParameterizedTerm1[As](Some(nameHint.valueOrAbort).filter(_.nonEmpty), expr, as)

private def unVarargs[T](args: Expr[Seq[T]])(using Quotes, Type[T], Reporting.Context): Seq[Expr[T]] =
  import quotes.reflect.*
  import Reporting.{badUse, treeStruct}
  inside(args.asTerm) {
    args match
      case Varargs(as) =>
        as
      case other =>
        val term = other.asTerm
        if (term.underlying eq term)
          badUse(s"Expected explicit arguments, got ${treeStruct(term)}")
        else
          unVarargs(other.asTerm.underlying.asExprOf[Seq[T]])
  }
