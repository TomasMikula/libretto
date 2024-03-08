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

    decode[As, Code] match
      case '[t] =>
        '{ (x: t) => x }
          .asExprOf[t => Box[As, Code]]

  private def unpackImpl[As, Code <: AnyKind](box: Expr[Box[As, Code]])(using
    Quotes,
    Type[As],
    Type[Code],
  ): Expr[Any] =
    decode[As, Code] match
      case '[t] => '{ $box.asInstanceOf[t] }


  // TODO: use report.errorAndAbort after https://github.com/lampepfl/dotty/issues/19851 is fixed
  private def errorAndAbort(msg: String)(using Quotes): Nothing =
    quotes.reflect.report.error(msg)
    ???

  def shortCode(using Quotes)(t: qr.TypeRepr): String =
    qr.Printer.TypeReprShortCode.show(t)

  def unsupportedType(using SourcePos, Quotes)(t: qr.TypeRepr): Nothing =
    unsupported(s"type ${shortCode(t)} (${qr.Printer.TypeReprStructure.show(t)})")

  def unsupported(using pos: SourcePos, q: Quotes)(msg: String): Nothing =
    errorAndAbort(s"Unsupported: $msg (at $pos).\nIf you have a use case for it, please request an enhancement.")

  def unimplemented(using pos: SourcePos, q: Quotes)(msg: String): Nothing =
    errorAndAbort(s"Unhandled case: $msg (at $pos).\n\nPlease, request an enhancement.")

  def badUse(using Quotes)(msg: String): Nothing =
    errorAndAbort(msg)

  def assertionFailed(using pos: SourcePos, q: Quotes)(msg: String): Nothing =
    errorAndAbort(s"Assertion failed: $msg (at $pos).\n\nPlease, report a bug.")

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
            badUse(s"Expected a type lambda, got ${shortCode(other)}")
      case other =>
        badUse(s"Expected a type lambda, got ${shortCode(other)}")

  private object Decoding {
    def apply(using q: Quotes)(): Decoding[q.type] =
      new Decoding[q.type]
  }
  private class Decoding[Q <: Quotes](using val q: Q) {
    import q.reflect.*

    enum ContextElem:
      case Substitution(src: TypeRepr, tgt: TypeRepr)

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
      ctx: List[ContextElem],
      body: TypeRepr,
    ): TypeRepr =
      body match
        case r @ Refinement(base, memName, memType) =>
          if (base =:= TypeRepr.of[PolyFunction]) {
            if (memName == "apply") {
              substInPolyFunType(marker, ctx, memType)
            } else {
              unsupportedType(r)
            }
          } else {
            unsupportedType(r)
          }
        case ref @ TypeRef(parent, name) =>
          checkNonOccurrence(marker, ctx, parent)
          ref
        case AppliedType(f, targs) =>
          // substitute in f
          val f1 = subst(marker, ctx, f)

          // expand type args
          val targs1 = expandTypeArgs(marker, ctx, targs)

          // f'[targs']
          AppliedType(f1, targs1)
        case t if t =:= marker =>
          // TODO: return a typed error and produce a better error message with a context of the wrongly used spread operator
          badUse(s"Cannot use the spread operator ${shortCode(marker)} in this position: ${shortCode(body)}")
        case p @ ParamRef(binder, i) =>
          ctx.collectFirst:
            case ContextElem.Substitution(src, tgt) if src =:= p => tgt
          match
            case Some(q) => q
            case None    => p
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

          def tParamBounds1(pt: PolyType): List[TypeBounds] =
            cont(pt.param)._1

          def paramTypes1(tparams: Int => TypeRepr): List[TypeRepr] =
            val ctx1 = cont(tparams)._2
            paramTypes.map(t => subst(marker, ctx1, t))

          def returnType1(tparams: Int => TypeRepr): TypeRepr =
            val ctx1 = cont(tparams)._2
            subst(marker, ctx1, returnType)

          polyFunType(
            tParamNames1,
            tParamBounds1,
            paramNames,
            paramTypes1,
            returnType1,
          )
        case other =>
          unsupported(s"PolyFunction refinement with apply method type ${shortCode(other)}")

    /** Function from type parameters to `R`. */
    private type TParamsFun[R] =
      (getTParam: Int => TypeRepr) => R

    private def substTypeParams(
      marker: TypeRepr,
      ctx: List[ContextElem],
      tParams: List[(String, TypeBounds, TypeRepr)],
    ): (List[String], TParamsFun[(List[TypeBounds], List[ContextElem])]) = {
      enum PostExpansionParam:
        case Original(name: String, bounds: TypeBounds)
        case Expanded(params: List[(String, TypeBounds)])

      def expandParam(name: String, kinds: TypeRepr): List[(String, TypeBounds)] =
        decodeKinds(kinds)
          .zipWithIndex
          .map { case (bounds, i) =>
            (name + "$" + i, bounds)
          }

      def expandParams(i: Int, ps: List[(String, TypeBounds, TypeRepr)]): List[(PostExpansionParam, (TypeRepr, TParamsFun[TypeRepr]))] =
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
                    val replacement: TParamsFun[TypeRepr] =
                      tparams => encodeTypeArgs(List.range(0, n).map(j => tparams(i + j)))
                    (PostExpansionParam.Expanded(expanded), (origType, replacement)) :: expandParams(i + n, ps)
                  case other =>
                    badUse(s"Cannot mix the \"spread\" upper bound (${shortCode(marker)}) with a lower bound (${shortCode(lower)})")
              case _ =>
                (PostExpansionParam.Original(name, bounds), (origType, _(i))) :: expandParams(i + 1, ps)

      val (expandedTParams, replacements): (List[PostExpansionParam], List[(TypeRepr, TParamsFun[TypeRepr])]) =
        expandParams(0, tParams).unzip

      val newSubstitutions: TParamsFun[List[ContextElem]] =
        tparams => replacements.map { case (origType, f) =>
          ContextElem.Substitution(origType, f(tparams))
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

    private def expandTypeArgs(
      marker: TypeRepr,
      ctx: List[ContextElem],
      targs: List[TypeRepr],
    ): List[TypeRepr] =
      targs.flatMap {
        case AppliedType(f, targs) =>
          if (f =:= marker) {
            targs match
              case a :: Nil =>
                val a1 = subst(marker, ctx, a)
                decodeTypeArgs(a1.asType)
                  .map(TypeRepr.of(using _))
              case other =>
                assertionFailed(s"Expected 1 type argument to ${shortCode(f)}, got ${targs.size} (${targs.map(shortCode).mkString(", ")})")
          } else {
            val f1 = subst(marker, ctx, f)
            val targs1 = expandTypeArgs(marker, ctx, targs)
            AppliedType(f1, targs1) :: Nil
          }
        case other =>
          subst(marker, ctx, other) :: Nil
      }

    private def substBounds(
      marker: TypeRepr,
      ctx: List[ContextElem],
      bounds: TypeBounds,
    ): TypeBounds =
      val TypeBounds(lo, hi) = bounds
      TypeBounds(
        subst(marker, ctx, lo),
        subst(marker, ctx, hi),
      )

    private def checkNonOccurrence(
      marker: TypeRepr,
      ctx: List[ContextElem],
      body: TypeRepr,
    ): Unit =
      body match
        case NoPrefix() =>
          ()
        case ThisType(t) =>
          checkNonOccurrence(marker, ctx, t)
        case TypeRef(parent, name) =>
          checkNonOccurrence(marker, ctx, parent)
        case TermRef(parent, name) =>
          checkNonOccurrence(marker, ctx, parent)
        case other =>
          unsupportedType(other)
  }
}
