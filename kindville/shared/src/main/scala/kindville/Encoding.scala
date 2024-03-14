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
    case TypeSubstitution(src: ParamRef | TypeRef, tgt: TypeRepr)
    case TypeArgExpansion(src: ParamRef | TypeRef, tgt: List[TypeRepr])
    case TermSubstitution(src: TermRef, tgt: Term)

    def show: String =
      this match
        case TypeSubstitution(src, tgt) => s"${typeShortCode(src)} -T> ${typeShortCode(tgt)}"
        case TermSubstitution(src, tgt) => s"${typeShortCode(src)} -E> ${treeShortCode(tgt)}"
        case TypeArgExpansion(src, tgt) => s"${typeShortCode(src)} --< ${tgt.map(typeShortCode)}"

  extension (ctx: List[ContextElem])
    def substitutesTypeTo: TypeSubstitutionExtractor = TypeSubstitutionExtractor(ctx)
    def substitutesTermTo: TermSubstitutionExtractor = TermSubstitutionExtractor(ctx)
    def expandsTo: ExpansionExtractor = ExpansionExtractor(ctx)

  class TypeSubstitutionExtractor(ctx: List[ContextElem]):
    def unapply(p: ParamRef | TypeRef): Option[TypeRepr] =
      ctx.collectFirst { case ContextElem.TypeSubstitution(src, res) if src =:= p =>
        println(s"Substituting ${typeShortCode(src)} (${typeStruct(src)}) --> ${typeShortCode(res)} (${typeStruct(res)})")
        report.info(s"Substituting ${typeShortCode(src)} --> ${typeShortCode(res)} (${typeStruct(res)})")
        res
      } match {
        case None =>
          println(s"No substition for ${typeShortCode(p)} in ${ctx.map(_.show)}")
          report.info(s"No substition for ${typeShortCode(p)} in ${ctx.map(_.show)}")
          None
        case res => res
      }

  class TermSubstitutionExtractor(ctx: List[ContextElem]):
    def unapply(i: Ident): Option[Term] =
      ctx.collectFirst { case ContextElem.TermSubstitution(src, res) if src.termSymbol == i.symbol => res } match
        case Some(res) => println(s"${i.show} -term-> ${res.show}"); Some(res)
        case None => println(s"No substitution for ${i.show} in ${ctx.map(_.show)}"); None

  class ExpansionExtractor(ctx: List[ContextElem]):
    def unapply(p: ParamRef | TypeRef): Option[List[TypeRepr]] =
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
                case (s, t) => ContextElem.TypeSubstitution(s, TypeRepr.of(using t))
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
    val res = doDecodeTerm(encoded)
    println(s"Decoded term: ${treeShortCode(res)}")
    println(s"Decoded term structure: ${treeStruct(res)}")
    res

  def doDecodeTerm[As](
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
              ContextElem.TypeSubstitution(typeRef, TypeRepr.of(using arg))
          }
        if (params.size != 1)
          badUse(s"Expected 1 value parameter of type Unit (to overcome Scala's implementation restriction of polymorphic functions). Got ${params.size}: ${params.map(_._1).mkString(", ")}")
        val dummyParam = params.head
        if (!dummyParam._1.startsWith("_$")) // compiler generated name for `_: T`
          badUse(s"The dummy parameter's name must be \"_\", was ${dummyParam._1}")
        decodeTerm(marker, substitutions, Symbol.spliceOwner, body)
      case i @ Inlined(_, _, _) =>
        decodeTerm[As](i.underlying)
      case other =>
        unimplemented(s"Term ${encoded.show(using Printer.TreeStructure)}")

  private def decodeType(
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
      case AppliedType(f, targs) =>
        val f1 = decodeType(marker, ctx, f)
        val targs1 = expandTypeArgs(marker, ctx, targs)
        val targs2 = targs1.map(decodeType(marker, ctx, _))
        f1.appliedTo(targs2)
      case t if t =:= marker =>
        // TODO: return a typed error and produce a better error message with a context of the wrongly used spread operator
        // badUse(s"Cannot use the spread operator ${typeShortCode(marker)} in this position: ${typeShortCode(body)}")
        badUse(s"Cannot use the spread operator here")
      case p: ParamRef =>
        p match
          case ctx.substitutesTypeTo(q) => q
          case ctx.expandsTo(ps)        => badUse(s"Invalid use of kind-expanded type argument ${typeShortCode(p)}. It can only be used in type argument position.")
          case p                        => p
      case t @ TypeRef(parent, name) =>
        t match
          case ctx.substitutesTypeTo(u) => u
          case ctx.expandsTo(ts)        => badUse(s"Invalid use of kind-expanded type argument ${typeShortCode(t)}. It can only be used in type argument position.")
          case t                        => checkNonOccurrence(marker, ctx, parent); t
      case other =>
        unsupportedType(other)

  private def decodeTerm(
    marker: TypeRef,
    ctx: List[ContextElem],
    owner: Symbol,
    expr: Term,
  ): Term =
    expr match
      case PolyFun(tparams, params, retTp, body) =>
        decodePolyFun(marker, ctx, tparams, params, retTp, body, owner)
      case bl @ Block(List(stmt), Closure(method, optTp)) =>
        (stmt, method) match
          case (DefDef(name, paramss, retTp, Some(body)), Ident(methodName)) if methodName == name =>
            paramss match
              case TermParamClause(params) :: Nil =>
                decodeFun(
                  marker,
                  ctx,
                  params.map { case v @ ValDef(name, tpe, _) => (name, tpe, v.symbol.termRef) },
                  retTp,
                  body,
                  owner,
                )
              case _ =>
                unsupported(s"Closure variant ${treeShortCode(bl)} (${treeStruct(bl)})")
          case _ =>
            unsupported(s"Closure variant ${treeShortCode(bl)} (${treeStruct(bl)})")
      case Apply(f, as) =>
        val f1 = decodeTerm(marker, ctx, owner, f)
        val bs = as.map(decodeTerm(marker, ctx, owner, _))
        Apply(f1, bs)
      case TypeApply(f, ts) =>
        val f1 = decodeTerm(marker, ctx, owner, f)
        val ts1 = expandTypeArgs(marker, ctx, ts.map(_.tpe))
        val ts2 = ts1.map(decodeType(marker, ctx, _))
        TypeApply(f1, ts2.map(t => TypeTree.of(using t.asType)))
      case Select(prefix, name) =>
        val prefix1 = decodeTerm(marker, ctx, owner, prefix)
        try {
          Select.unique(prefix1, name)
        } catch {
          e => unsupported(s"x.m for overloaded m. In ${treeShortCode(prefix1)}.$name")
        }
      case i @ Ident(x) =>
        i match
          case ctx.substitutesTermTo(j) => j
          case i => i
      case l: Literal =>
        l
      case other =>
        unimplemented(s"decodeTerm(${treeStruct(expr)})")

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
                    (n, Left(b), pi)
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

  private def decodePolyFun(
    marker: TypeRef,
    ctx: List[ContextElem],
    tparams: List[(String, TypeBoundsTree | LambdaTypeTree, TypeRef)], // (name, kind, reference)
    params: List[(String, TypeTree, TermRef)],
    returnType: TypeTree,
    body: Term,
    owner: Symbol,
  ): Term = {
    val (tParamNames1, cont) =
      decodeTypeParams(
        marker,
        ctx,
        tparams map { case (n, t, ref) =>
          t match
            case b: TypeBoundsTree => (n, Left(b.tpe), ref)
            case l: LambdaTypeTree => (n, Right(l), ref)
        }
      )

    def tParamBounds1(pt: PolyType): List[TypeBounds] =
      cont(pt.param)._1

    val paramNames = params.map(_._1)

    def paramTypes(tparams: Int => TypeRepr): List[TypeRepr] =
      val ctx1 = cont(tparams)._2
      params.map(t => decodeType(marker, ctx1, t._2.tpe))

    def returnType1(tparams: Int => TypeRepr): TypeRepr =
      val ctx1 = cont(tparams)._2
      decodeType(marker, ctx1, returnType.tpe)

    def paramSubstitutions(newParams: List[Term]): List[ContextElem.TermSubstitution] =
      (params zip newParams).map { case (pOld, pNew) =>
        ContextElem.TermSubstitution(pOld._3, pNew)
      }

    def body1(newTParams: Int => TypeRepr, newParams: List[Term], owner: Symbol): Term =
      val ctx1 = cont(newTParams)._2
      val ctx2 = paramSubstitutions(newParams) ::: ctx1
      decodeTerm(marker, ctx2, owner, body)

    PolyFun(tParamNames1, tParamBounds1, paramNames, paramTypes, returnType1, body1, owner)
  }

  private def decodeFun(
    marker: TypeRef,
    ctx: List[ContextElem],
    params: List[(String, TypeTree, TermRef)],
    returnType: TypeTree,
    body: Term,
    owner: Symbol,
  ): Term = {

    val paramNames = params.map(_._1)

    val paramTypes =
      params.map(t => decodeType(marker, ctx, t._2.tpe))

    val returnType1: TypeRepr =
      decodeType(marker, ctx, returnType.tpe)

    def paramSubstitutions(newParams: List[Term]): List[ContextElem.TermSubstitution] =
      (params zip newParams).map { case (pOld, pNew) =>
        ContextElem.TermSubstitution(pOld._3, pNew)
      }

    def body1(newParams: List[Term], owner: Symbol): Term =
      val ctx1 = paramSubstitutions(newParams) ::: ctx
      decodeTerm(marker, ctx1, owner, body)

    val methSym =
      Symbol.newMethod(
        owner,
        name = "functionImpl",
        tpe = MethodType(paramNames)(_ => paramTypes, _ => returnType1),
      )

    val meth =
      DefDef(
        methSym,
        rhsFn = { case List(argTrees) =>
          val args = argTrees.map(_.asInstanceOf[Term])
          Some(body1(args, methSym))
        }
      )

    Block(
      List(meth),
      Closure(Ident(methSym.termRef), tpe = None),
    )
  }

  /** Function from type parameters to `R`. */
  private type TParamsFun[R] =
    (getTParam: Int => TypeRepr) => R

  private def decodeTypeParams(
    marker: TypeRepr,
    ctx: List[ContextElem],
    tParams: List[(String, Either[TypeBounds, LambdaTypeTree], ParamRef | TypeRef)],
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
      ps: List[(String, Either[TypeBounds, LambdaTypeTree], ParamRef | TypeRef)],
    ): List[(PostExpansionParam, TParamsFun[ContextElem])] =
      ps match
        case Nil =>
          Nil
        case (name, Left(TypeBounds(lower, upper)), origParam) :: ps =>
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
              val bounds1 = TypeBounds(decodeType(marker, ctx, lower), decodeType(marker, ctx, upper))
              ( PostExpansionParam.Original(name, bounds1)
              , tps => ContextElem.TypeSubstitution(origParam, tps(i))
              ) :: expandParams(i + 1, ps)
        case (name, Right(ltt), origParam) :: ps =>
          unimplemented(s"decoding of $name <: ${treeStruct(ltt)}")

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
      case fa @ AppliedType(f, targs) =>
        if (f =:= marker) {
          // encode the expanded argument (A --> A1, ...) into a single type A1 :: ...
          targs match
            case a :: Nil =>
              // lookup in the substitution for `a` in context
              unimplemented(s"encoding an expanded type argument into a single type")
            case other =>
              assertionFailed(s"Expected 1 type argument to ${typeShortCode(f)}, got ${targs.size} (${targs.map(typeShortCode).mkString(", ")})")
        } else {
          fa :: Nil
        }
      case p: ParamRef =>
        p match
          case ctx.expandsTo(ps) => ps
          case _                 => p :: Nil
      case t: TypeRef =>
        t match
          case ctx.expandsTo(ts) => ts
          case _                 => t :: Nil
      case other =>
        other :: Nil
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
