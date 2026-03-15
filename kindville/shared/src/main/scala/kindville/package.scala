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

transparent inline def decode(inline expr: [⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any)(inline args: Any*): Any =
  ${ decodeNamedImpl('{""}, 'expr, 'args) }

transparent inline def decodeT[As](inline expr: [⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any)(inline args: Any*): Any =
  decodeFull(nameHint = "")[[⋅⋅[_]] =>> As](expr)(args*)

transparent inline def decodeNamed(nameHint: String)(inline expr: [⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any)(inline args: Any*): Any =
  ${ decodeNamedImpl('nameHint, 'expr, 'args) }

transparent inline def decodeTNamed(nameHint: String)[As](inline expr: [⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any)(inline args: Any*): Any =
  decodeFull(nameHint)[[⋅⋅[_]] =>> As](expr)(args*)

transparent inline def decodeFull(nameHint: String)[As[⋅⋅[_]]](inline expr: [⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any)(inline args: Any*): Any =
  ${ decodeFullImpl[As]('nameHint, 'expr, 'args) }

private def decodeNamedImpl(nameHint: Expr[String], expr: Expr[[⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any], args: Expr[Seq[Any]])(using Quotes): Expr[Any] =
  insideMacroExpansion:
    import quotes.reflect.*
    val encoding = Encoding()
    val as = unVarargs(args).toList
    encoding
      .decodeParameterizedTerm0(Some(nameHint.valueOrAbort).filter(_.nonEmpty), expr, as)

private def decodeFullImpl[As[⋅⋅[_]]](nameHint: Expr[String], expr: Expr[[⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any], args: Expr[Seq[Any]])(using Quotes, Type[As]): Expr[Any] =
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

extension [A](inline a: A)
  inline def typecheckAs[B]: B =
    ${ typecheckAsImpl[A, B]('a) }

private def typecheckAsImpl[A, B](a: Expr[A])(using Quotes, Type[B]): Expr[B] =
  a.asExprOf[B]
