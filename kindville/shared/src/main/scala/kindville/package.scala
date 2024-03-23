package kindville

import scala.quoted.*
import scala.PolyFunction
import scala.annotation.experimental

sealed trait *
sealed trait -->[K, L]
type ->[K, L] = (K :: TNil) --> L

sealed trait ::[H <: AnyKind, T]
sealed trait TNil

infix sealed trait ofKind[F <: AnyKind, K]
infix sealed trait ofKinds[As, Ks]

private transparent inline def qr(using Quotes): quotes.reflect.type =
  quotes.reflect

transparent inline def decodeFun(funcode: Any): Any =
  ${ decodeFunImpl('funcode) }

transparent inline def decodeExpr[As](expr: Any)(inline args: Any*): Any =
  ${ decodeExprImpl[As]('expr, 'args) }

private def decodeFunImpl(funcode: Expr[Any])(using Quotes): Expr[Any] =
  val encoding = Encoding()
  encoding.decodeTerm(funcode)

private def decodeExprImpl[As](expr: Expr[Any], args: Expr[Seq[Any]])(using Quotes, Type[As]): Expr[Any] =
  import quotes.reflect.*
  val encoding = Encoding()
  val as = unVarargs(args).toList
  encoding
    .decodeParameterizedTerm[As](expr, as)

private def unVarargs[T](args: Expr[Seq[T]])(using Quotes, Type[T]): Seq[Expr[T]] =
  import quotes.reflect.*
  import Reporting.{badUse, treeStruct}
  args match
    case Varargs(as) =>
      as
    case other =>
      val term = other.asTerm
      if (term.underlying eq term)
        badUse(s"Expected explicit arguments, got ${treeStruct(term)}")
      else
        unVarargs(other.asTerm.underlying.asExprOf[Seq[T]])
