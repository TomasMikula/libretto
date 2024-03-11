package kindville

import scala.quoted.*
import kindville.Reporting.*

private object Encoding {
  def apply(using q: Quotes)(): Encoding[q.type] =
    new Encoding[q.type]
}

private class Encoding[Q <: Quotes](using val q: Q) {
  import q.reflect.*

  enum ContextElem:
    case Substitution(src: ParamRef | TypeRef, tgt: TypeRepr)
    case TypeArgExpansion(src: ParamRef, tgt: List[TypeRepr])

  extension (ctx: List[ContextElem])
    def substitutesTo: SubstitutionExtractor = SubstitutionExtractor(ctx)
    def expandsTo: ExpansionExtractor = ExpansionExtractor(ctx)

  class SubstitutionExtractor(ctx: List[ContextElem]):
    def unapply(p: ParamRef): Option[TypeRepr] =
      ctx.collectFirst { case ContextElem.Substitution(src, res) if src =:= p => res }

  class ExpansionExtractor(ctx: List[ContextElem]):
    def unapply(p: ParamRef): Option[List[TypeRepr]] =
      ctx.collectFirst { case ContextElem.TypeArgExpansion(src, res) if src =:= p => res }

  def unsupportedType(using SourcePos, Quotes)(t: qr.TypeRepr): Nothing =
    unsupported(s"type ${typeShortCode(t)} (${qr.Printer.TypeReprStructure.show(t)})")

  def unexpectedTypeParamType(using pos: SourcePos, q: Quotes)(t: qr.TypeRepr): Nothing =
    assertionFailed(s"a type parameter that is not a ParamRef. Was ${qr.Printer.TypeReprStructure.show(t)}")

  def decodeType[As, Code <: AnyKind](using
    Type[As],
    Type[Code],
  ): Type[Any] =
    val args = decodeTypeArgs(Type.of[As])

    TypeRepr.of[Code].dealias match
      case outer @ TypeLambda(auxNames, auxBounds, body) =>
        val List(_) = auxNames
        val List(_) = auxBounds
        val marker = outer.param(0)
        body match
          case inner @ TypeLambda(paramNames, paramBounds, body) =>
            require(paramNames.size == args.size)
            val params =
              List.range(0, args.size).map { i =>
                inner.param(i) match
                  case pi @ ParamRef(_, _) => pi
                  case other => unexpectedTypeParamType(other)
              }
            val substitutions =
              (params zip args) map {
                case (s, t) => ContextElem.Substitution(s, TypeRepr.of(using t))
              }
            decodeType(marker, substitutions, body)
              .asType
              .asInstanceOf[Type[Any]]
          case other =>
            badUse(s"Expected a type lambda, got ${typeShortCode(other)}")
      case other =>
        badUse(s"Expected a type lambda, got ${typeShortCode(other)}")

  def decodeTerm[As](
    encoded: Term,
  )(using
    Type[As],
  ): Term =
    val args = decodeTypeArgs(Type.of[As])

    encoded match
      case PolyFun(tparams, params, retTp, body) =>
        if (tparams.isEmpty)
          assertionFailed("unexpected polymorphic function with 0 type parameters")
        val (name, kind, typeRef) = tparams.head
        val userTParams = tparams.tail
        val marker = typeRef // TODO: check that marker has kind _[_]
        if (userTParams.size != args.size)
          badUse(s"Expected ${args.size} custom type parameters matching the arguments ${args.map(t => typeShortCode(t)).mkString(", ")}. Got ${userTParams.map(p => typeShortCode(p._3)).mkString(", ")}")
        val substitutions =
          (userTParams zip args) map {
            case ((_, _, typeRef), arg) =>
              ContextElem.Substitution(typeRef, TypeRepr.of(using arg))
          }
        if (params.size != 1)
          badUse(s"Expected 1 value parameter of type Unit (to overcome Scala's implementation restriction of polymorphic functions). Got ${params.size}: ${params.map(_._1).mkString(", ")}")
        val dummyParam = params.head
        if (dummyParam._1 != "_")
          badUse(s"The dummy parameter's name must be \"_\", was ${dummyParam._1}")
        // decodeTerm(marker, substitutions, body)
        unimplemented("polymorphic function")
      case i @ Inlined(_, _, _) =>
        decodeTerm[As](i.underlying)
      case other =>
        unimplemented(s"Term ${encoded.show(using Printer.TreeStructure)}")

  def decodeType(
    marker: TypeRepr,
    ctx: List[ContextElem],
    body: TypeRepr,
  ): TypeRepr =
    body match
      case r @ Refinement(base, memName, memType) =>
        if (base =:= TypeRepr.of[PolyFunction]) {
          if (memName == "apply") {
            decodePolyFunType(marker, ctx, memType)
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
        val f1 = decodeType(marker, ctx, f)

        // expand type args
        val targs1 = expandTypeArgs(marker, ctx, targs)

        // f'[targs']
        AppliedType(f1, targs1)
      case t if t =:= marker =>
        // TODO: return a typed error and produce a better error message with a context of the wrongly used spread operator
        badUse(s"Cannot use the spread operator ${typeShortCode(marker)} in this position: ${typeShortCode(body)}")
      case p @ ParamRef(_, _) =>
        p match
          case ctx.substitutesTo(q) => q
          case ctx.expandsTo(qs)    => badUse(s"Invalid use of kind-expanded type argument ${typeShortCode(p)}. It can only be used in type argument position.")
          case p                    => p
      case other =>
        unsupportedType(other)

  private def decodePolyFunType(
    marker: TypeRepr,
    ctx: List[ContextElem],
    methType: TypeRepr,
  ): TypeRepr =
    methType match
      case pt @ PolyType(tParamNames, tParamBounds, MethodType(paramNames, paramTypes, returnType)) =>
        val (tParamNames1, cont) =
          decodeTypeParams(
            marker,
            ctx,
            (tParamNames zip tParamBounds).zipWithIndex map {
              case ((n, b), i) =>
                pt.param(i) match
                  case pi @ ParamRef(_, _) =>
                    (n, b, pi)
                  case other =>
                    unexpectedTypeParamType(other)
            },
          )

        def tParamBounds1(pt: PolyType): List[TypeBounds] =
          cont(pt.param)._1

        def paramTypes1(tparams: Int => TypeRepr): List[TypeRepr] =
          val ctx1 = cont(tparams)._2
          paramTypes.map(t => decodeType(marker, ctx1, t))

        def returnType1(tparams: Int => TypeRepr): TypeRepr =
          val ctx1 = cont(tparams)._2
          decodeType(marker, ctx1, returnType)

        PolyFun.mkType(
          tParamNames1,
          tParamBounds1,
          paramNames,
          paramTypes1,
          returnType1,
        )
      case other =>
        unsupported(s"PolyFunction refinement with apply method type ${typeShortCode(other)}")

  /** Function from type parameters to `R`. */
  private type TParamsFun[R] =
    (getTParam: Int => TypeRepr) => R

  private def decodeTypeParams(
    marker: TypeRepr,
    ctx: List[ContextElem],
    tParams: List[(String, TypeBounds, ParamRef)],
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

    def expandParams(
      i: Int,
      ps: List[(String, TypeBounds, ParamRef)],
    ): List[(PostExpansionParam, TParamsFun[ContextElem])] =
      ps match
        case Nil =>
          Nil
        case (name, bounds @ TypeBounds(lower, upper), origParam) :: ps =>
          upper match
            case AppliedType(f, List(kinds)) if f =:= marker =>
              lower.asType match
                case '[Nothing] =>
                  val expanded = expandParam(name, kinds)
                  val n = expanded.size
                  val replacement: TParamsFun[ContextElem] =
                    tparams => ContextElem.TypeArgExpansion(origParam, List.range(0, n).map(j => tparams(i + j)))
                  (PostExpansionParam.Expanded(expanded), replacement) :: expandParams(i + n, ps)
                case other =>
                  badUse(s"Cannot mix the \"spread\" upper bound (${typeShortCode(marker)}) with a lower bound (${typeShortCode(lower)})")
            case _ =>
              (PostExpansionParam.Original(name, bounds), tps => ContextElem.Substitution(origParam, tps(i))) :: expandParams(i + 1, ps)

    val (expandedTParams, replacements): (List[PostExpansionParam], List[TParamsFun[ContextElem]]) =
      expandParams(0, tParams).unzip

    val newSubstitutions: TParamsFun[List[ContextElem]] =
      tparams => replacements.map(_(tparams))

    val (names, bounds) =
      expandedTParams.flatMap:
        case PostExpansionParam.Original(name, bounds) => (name, bounds) :: Nil
        case PostExpansionParam.Expanded(params)       => params
      .unzip

    (names, pt => {
      val ctx1 = newSubstitutions(pt) ::: ctx
      val bounds1 = bounds.map(decodeTypeBounds(marker, ctx1, _))
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
          // encode the expanded argument (A --> A1, ...) into a single type A1 :: ...
          targs match
            case a :: Nil =>
              // lookup in the substitution for `a` in context
              unimplemented(s"encoding an expanded type argument into a single type")
            case other =>
              assertionFailed(s"Expected 1 type argument to ${typeShortCode(f)}, got ${targs.size} (${targs.map(typeShortCode).mkString(", ")})")
        } else {
          val f1 = decodeType(marker, ctx, f)
          val targs1 = expandTypeArgs(marker, ctx, targs)
          AppliedType(f1, targs1) :: Nil
        }
      case p @ ParamRef(_, _) =>
        ctx
          .collectFirst {
            case ContextElem.TypeArgExpansion(src, res) if src =:= p =>
              res
          }
          .getOrElse(decodeType(marker, ctx, p) :: Nil)
      case other =>
        decodeType(marker, ctx, other) :: Nil
    }

  private def decodeTypeBounds(
    marker: TypeRepr,
    ctx: List[ContextElem],
    bounds: TypeBounds,
  ): TypeBounds =
    val TypeBounds(lo, hi) = bounds
    TypeBounds(
      decodeType(marker, ctx, lo),
      decodeType(marker, ctx, hi),
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
