package kindville

import scala.quoted.*

opaque type Box[As, Code <: AnyKind] = Any

object Box {
  transparent inline def pack[As, Code <: AnyKind]: Nothing => Box[As, Code] =
    ${ packImpl[As, Code] }

  transparent inline def unpack[As, Code <: AnyKind](box: Box[As, Code]): Any =
    ${ unpackImpl[As, Code]('box) }

  private def packImpl[As, Code <: AnyKind](using
    Quotes,
    Type[As],
    Type[Code],
  ): Expr[Nothing => Box[As, Code]] =
    import quotes.reflect.*

    '{ (x: Any) => x }
      .asExprOf(using
        TypeRepr
          .of[Function]
          .appliedTo(
            List(
              TypeRepr.of(using decode[As, Code]),
              TypeRepr.of[Box[As, Code]],
            )
          )
          .asType
          .asInstanceOf[Type[Nothing => Box[As, Code]]]
      )

  private def unpackImpl[As, Code <: AnyKind](box: Expr[Box[As, Code]])(using
    Quotes,
    Type[As],
    Type[Code],
  ): Expr[Any] =
    box.asExprOf(using decode[As, Code])

  // TODO: use report.errorAndAbort after https://github.com/lampepfl/dotty/issues/19851 is fixed
  private def errorAndAbort(msg: String)(using Quotes): Nothing =
    quotes.reflect.report.error(msg)
    ???

  private def decode[As, Code <: AnyKind](using
    Quotes,
    Type[As],
    Type[Code],
  ): Type[Any] =
    import quotes.reflect.*

    val args = decodeTypeArgs(Type.of[As])

    TypeRepr.of[Code].dealias match
      case outer @ TypeLambda(auxNames, auxBounds, body) =>
        val List(_) = auxNames
        val List(_) = auxBounds
        val marker = outer.param(0)
        body match
          case inner @ TypeLambda(paramNames, paramBounds, body) =>
            require(paramNames.size == args.size)
            val params = List.range(0, args.size).map(inner.param(_))
            val substitutions = params zip (args.map(TypeRepr.of(using _)))
            val decoding: Decoding[quotes.type] = Decoding()
            decoding
              .substitute(substitutions, body)
              .asType
              .asInstanceOf[Type[Any]]
      case other =>
        errorAndAbort(s"Expected a type lambda, got ${Printer.TypeReprShortCode.show(other)}")

  private object Decoding {
    def apply(using q: Quotes)(): Decoding[q.type] =
      new Decoding[q.type]
  }
  private class Decoding[Q <: Quotes](using val q: Q) {
    import q.reflect.*

    enum ContextElem:
      case Substitution(src: TypeRepr, tgt: TypeRepr)

    def unsupportedType(using SourcePos)(t: TypeRepr): Nothing =
      unsupported(s"type ${Printer.TypeReprShortCode.show(t)}")

    def unsupported(using pos: SourcePos)(msg: String): Nothing =
      errorAndAbort(s"Unsupported: $msg (at $pos)")

    def unimplemented(using pos: SourcePos): Nothing =
      unimplemented("Not yet implemented")

    def unimplemented(using pos: SourcePos)(msg: String): Nothing =
      errorAndAbort(s"$msg (at $pos)")

    def shortCode(t: TypeRepr): String =
      Printer.TypeReprShortCode.show(t)

    def substitute(
      substitutions: List[(TypeRepr, TypeRepr)],
      body: TypeRepr,
    ): TypeRepr =
      subst(
        substitutions.map { case (s, t) => ContextElem.Substitution(s, t) },
        body
      )

    def subst(
      context: List[ContextElem],
      body: TypeRepr,
    ): TypeRepr =
      body match
        case r @ Refinement(base, memName, memType) =>
          if (base =:= TypeRepr.of[PolyFunction]) {
            if (memName == "apply") {
              substInPolyFunType(memType)
            } else {
              unsupportedType(r)
            }
          } else {
            unsupportedType(r)
          }
        case other =>
          unsupportedType(other)

    private def substInPolyFunType(methType: TypeRepr): TypeRepr =
      methType match
        case PolyType(tParamNames, tParamBounds, MethodType(paramNames, paramTypes, returnType)) =>
          unimplemented(s"${shortCode(methType)}")
        case other =>
          unsupported(s"PolyFunction refinement with apply method type ${shortCode(other)}")
  }
}
