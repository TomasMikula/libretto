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

transparent inline def decodeFun(funcode: Any): Any =
  ${ decodeFunImpl('funcode) }

transparent inline def decodeExpr[As](expr: Any)(inline args: Any*): Any =
  decodeCompositeExpr[[⋅⋅[_]] =>> As](expr)(args*)

transparent inline def decodeExpr1[As](expr: [⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any)(inline args: Any*): Any =
  decodeCompositeExpr1(nameHint = "")[[⋅⋅[_]] =>> As](expr)(args*)

transparent inline def decodeExprNamed(nameHint: String)[As](expr: [⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any)(inline args: Any*): Any =
  decodeCompositeExpr1(nameHint)[[⋅⋅[_]] =>> As](expr)(args*)

transparent inline def decodeCompositeExpr[As[⋅⋅[_]]](expr: Any)(inline args: Any*): Any =
  ${ decodeCompositeExprImpl[As]('expr, 'args) }

transparent inline def decodeCompositeExpr1(nameHint: String)[As[⋅⋅[_]]](expr: [⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any)(inline args: Any*): Any =
  ${ decodeCompositeExprImpl1[As]('nameHint, 'expr, 'args) }

private def decodeFunImpl(funcode: Expr[Any])(using Quotes): Expr[Any] =
  insideMacroExpansion:
    val encoding = Encoding()
    encoding.decodeFun(funcode)

private def decodeCompositeExprImpl[As[⋅⋅[_]]](expr: Expr[Any], args: Expr[Seq[Any]])(using Quotes, Type[As]): Expr[Any] =
  insideMacroExpansion:
    import quotes.reflect.*
    val encoding = Encoding()
    val as = unVarargs(args).toList
    encoding
      .decodeParameterizedTerm[As](expr, as)

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

extension (a: Any) {
  inline def typecheck[T]: T =
    ${ typecheckImpl[T]('a) }

  /**
   * @tparam As list of type arguments (`A :: B :: ... :: TNil`)
   * @tparam Res expected result type. The result will be typechecked against this type.
   * @param bs value argument
   */
  inline def polyFunApply[As, Res](bs: Any*): Res =
    ${ polyFunApplyImpl[As, Res]('a, 'bs) }
}

private def typecheckImpl[T](a: Expr[Any])(using Quotes, Type[T]): Expr[T] =
  insideMacroExpansion {
    import qr.*

    if   a.isExprOf[T]
    then a.asExprOf[T]
    else Reporting.badUse(
      s"""${a.show}
        |  with underlying tree ${a.asTerm.underlying.show}
        |  of type ${a.asTerm.tpe.show}
        |  does not conform to type
        |  ${TypeRepr.of[T].show}.
        |""".stripMargin
    )
  }

private def polyFunApplyImpl[Ts, R](
  f: Expr[Any],
  args: Expr[Seq[Any]],
)(using
  Quotes,
  Type[Ts],
  Type[R],
): Expr[R] =
  insideMacroExpansion {
    import qr.*
    val ts = Encoding.decodeTypeArgs[Ts](Type.of[Ts]).map(TypeRepr.of(using _))
    val as = unVarargs(args).toList
    Select
      .unique(f.asTerm, "apply")
      .appliedToTypes(ts)
      .appliedToArgs(as.map(_.asTerm))
      .asExprOf[R]
  }
