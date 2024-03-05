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
              .substitute(marker, substitutions, body)
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

    def unimplemented(using pos: SourcePos)(msg: String): Nothing =
      errorAndAbort(s"Not yet implemented: $msg (at $pos)")

    def badUse(msg: String): Nothing =
      errorAndAbort(msg)

    def shortCode(t: TypeRepr): String =
      Printer.TypeReprShortCode.show(t)

    def substitute(
      marker: TypeRepr,
      substitutions: List[(TypeRepr, TypeRepr)],
      body: TypeRepr,
    ): TypeRepr =
      subst(
        marker,
        substitutions.map { case (s, t) => ContextElem.Substitution(s, t) },
        body
      )

    def subst(
      marker: TypeRepr,
      context: List[ContextElem],
      body: TypeRepr,
    ): TypeRepr =
      body match
        case r @ Refinement(base, memName, memType) =>
          if (base =:= TypeRepr.of[PolyFunction]) {
            if (memName == "apply") {
              substInPolyFunType(marker, context, memType)
            } else {
              unsupportedType(r)
            }
          } else {
            unsupportedType(r)
          }
        case other =>
          unsupportedType(other)

    private def substInPolyFunType(
      marker: TypeRepr,
      ctx: List[ContextElem],
      methType: TypeRepr,
    ): TypeRepr =
      methType match
        case pt @ PolyType(tParamNames, tParamBounds, MethodType(paramNames, paramTypes, returnType)) =>
          val (tParamNames1, cont) =
            substTypeParams(
              marker,
              ctx,
              (tParamNames zip tParamBounds).zipWithIndex map {
                case ((n, b), i) => (n, b, pt.param(i))
              },
            )
          unimplemented(s"${shortCode(methType)}")
        case other =>
          unsupported(s"PolyFunction refinement with apply method type ${shortCode(other)}")

    private def substTypeParams(
      marker: TypeRepr,
      ctx: List[ContextElem],
      tParams: List[(String, TypeBounds, TypeRepr)],
    ): (List[String], PolyType => (List[TypeBounds], List[ContextElem])) = {
      enum PostExpansionParam:
        case Original(name: String, bounds: TypeBounds)
        case Expanded(params: List[(String, TypeBounds)])

      def expandParam(name: String, kinds: TypeRepr): List[(String, TypeBounds)] =
        decodeKinds(kinds)
          .zipWithIndex
          .map { case (bounds, i) =>
            (name + "$" + i, bounds)
          }

      def expandParams(i: Int, ps: List[(String, TypeBounds, TypeRepr)]): List[(PostExpansionParam, (TypeRepr, PolyType => TypeRepr))] =
        ps match
          case Nil =>
            Nil
          case (name, bounds @ TypeBounds(lower, upper), origType) :: ps =>
            upper match
              case AppliedType(f, List(kinds)) if f =:= marker =>
                lower.asType match
                  case '[Nothing] =>
                    val expanded = expandParam(name, kinds)
                    val n = expanded.size
                    val replacement: PolyType => TypeRepr =
                      pt => encodeTypeArgs(List.range(0, n).map(j => pt.param(i + j)))
                    (PostExpansionParam.Expanded(expanded), (origType, replacement)) :: expandParams(i + n, ps)
                  case other =>
                    badUse(s"Cannot mix the \"spread\" upper bound (${shortCode(marker)}) with a lower bound (${shortCode(lower)})")
              case _ =>
                (PostExpansionParam.Original(name, bounds), (origType, _.param(i))) :: expandParams(i + 1, ps)

      val (expandedTParams, replacements): (List[PostExpansionParam], List[(TypeRepr, PolyType => TypeRepr)]) =
        expandParams(0, tParams).unzip

      val newSubstitutions: PolyType => List[ContextElem] =
        pt => replacements.map { case (origType, f) =>
          ContextElem.Substitution(origType, f(pt))
        }

      val (names, bounds) =
        expandedTParams.flatMap:
          case PostExpansionParam.Original(name, bounds) => (name, bounds) :: Nil
          case PostExpansionParam.Expanded(params)       => params
        .unzip

      (names, pt => {
        val ctx1 = newSubstitutions(pt) ::: ctx
        val bounds1 = bounds.map(substBounds(marker, ctx1, _))
        (bounds1, ctx1)
      })
    }

    private def substBounds(
      marker: TypeRepr,
      ctx: List[ContextElem],
      bounds: TypeBounds,
    ): TypeBounds =
      unimplemented(s"substBounds")
  }
}
