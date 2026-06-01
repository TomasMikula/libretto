package kindville

import kindville.Reporting.*
import kindville.SingleOrMultiple.{Multiple, Single}
import scala.quoted.*

private object Encoding {
  def apply(using q: Quotes)(): Encoding[q.type] =
    new Encoding[q.type]

  extension [A](as: List[A]) {
    def mapS[S, B](s: S)(f: (S, A) => (S, B)): (S, List[B]) =
      as match
        case Nil =>
          (s, Nil)
        case a :: as =>
          val (s1, b) = f(s, a)
          val (s2, bs) = as.mapS(s1)(f)
          (s2, b :: bs)
  }

  def bundleTypeArgs(using Quotes)(args: List[quotes.reflect.TypeRepr]): quotes.reflect.TypeRepr =
    import quotes.reflect.*
    args match
      case Nil => TypeRepr.of[TNil]
      case t :: ts => TypeRepr.of[::].appliedTo(List(t, bundleTypeArgs(ts)))

  def unbundleTypeArgs[As <: AnyKind](args: Type[As])(using Quotes): List[Type[?]] =
    import quotes.reflect.*

    val cons = TypeRepr.of[::]

    args match
      case '[TNil] => Nil
      case other =>
        val repr = TypeRepr.of(using other)
        repr match
          case AppliedType(f, args) =>
            f.asType match
              case '[::] =>
                args match
                  case h :: t :: Nil =>
                    h.asType :: unbundleTypeArgs(t.asType)(using quotes)
                  case _ =>
                    report.errorAndAbort(s"Unexpected number of type arguments to ${Printer.TypeReprShortCode.show(f)}. Expected 2, got ${args.size}: ${args.map(Printer.TypeReprShortCode.show(_).mkString(", "))}")
              case other =>
                report.error(s"Cannot decode a list of type arguments from type ${Printer.TypeReprShortCode.show(repr)}")
                Nil
          case other =>
            report.error(s"Cannot decode a list of type arguments from type ${Printer.TypeReprShortCode.show(repr)}")
            Nil

  private enum FastReject[A]:
    case Success(value: A)
    case Reject(expectedOneOf: List[String])

  def decodeKind(using Quotes, Reporting.Context)(k: qr.TypeRepr): Kind =
    import qr.*
    inside(k):
      decodeKind__(k) match
        case FastReject.Success(res) =>
          res
        case FastReject.Reject(expectedOneOf) =>
          badUse(s"Could not decode ${Printer.TypeReprShortCode.show(k)} as a kind. Expected one of ${expectedOneOf.mkString(", ")}")

  private def decodeKind__(using Quotes, Reporting.Context)(k: qr.TypeRepr): FastReject[Kind] =
    import qr.*

    k.dealiasKeepOpaques match
      case tp if tp =:= TypeRepr.of[*] =>
        FastReject.Success(Kind.Tp)
      case AppliedType(f, args) if f =:= TypeRepr.of[->>] =>
        args match
          case inKs :: outK :: Nil =>
            FastReject.Success:
              val in = decodeKindOrKinds(inKs)
              val ks = in.left.map(Kinds.single).merge
              val l  = decodeKind(outK)
              Kind.arr(ks, l)
          case _ =>
            assertionFailed(s"Unexpected number of type arguments to ${Printer.TypeReprShortCode.show(f)}. Expected 2, got ${args.size}: ${args.map(Printer.TypeReprShortCode.show(_).mkString(", "))}")
      case other =>
        FastReject.Reject(expectedOneOf = List(typeShortCode(TypeRepr.of[*]), typeShortCode(TypeRepr.of[->>])))

  def decodeKinds(using Quotes, Reporting.Context)(kinds: qr.TypeRepr): Kinds =
    import qr.*
    inside(kinds):
      decodeKinds__(kinds) match
        case FastReject.Success(res) =>
          res
        case FastReject.Reject(expectedOneOf) =>
          badUse(s"Cannot decode ${Printer.TypeReprShortCode.show(kinds)} as a list of kinds. Expected one of ${expectedOneOf.mkString(", ")}")

  private def decodeKinds__(using Quotes, Reporting.Context)(kinds: qr.TypeRepr): FastReject[Kinds] =
    import qr.*

    kinds.dealiasKeepOpaques match
      case tnil if tnil =:= TypeRepr.of[TNil] =>
        FastReject.Success(Kinds.Empty)
      case AppliedType(f, args) if f =:= TypeRepr.of[::] =>
        args match
          case k :: ks :: Nil =>
            FastReject.Success:
              val k1  = decodeKind(k)
              val ks1 = decodeKinds(ks)
              k1 :: ks1
          case _ =>
            assertionFailed(s"Unexpected number of type arguments to ${Printer.TypeReprShortCode.show(f)}. Expected 2, got ${args.size}: ${args.map(Printer.TypeReprShortCode.show(_).mkString(", "))}")
      case other =>
        FastReject.Reject(expectedOneOf = List(typeShortCode[TNil], typeShortCode[::]))

  def decodeKindOrKinds(using Quotes, Reporting.Context)(ks: qr.TypeRepr): Either[Kind, Kinds] =
    import qr.*

    inside(ks):
      decodeKind__(ks) match
        case FastReject.Success(k) => Left(k)
        case FastReject.Reject(expectedOneOf1) =>
          decodeKinds__(ks) match
            case FastReject.Success(ks) => Right(ks)
            case FastReject.Reject(expectedOneOf2) =>
              badUse(s"Could not decode ${Printer.TypeReprShortCode.show(ks)} as a kind(s). Expected one of ${(expectedOneOf1 ++ expectedOneOf2).mkString(", ")}")

  def kindToBounds(k: Kind)(using Quotes): qr.TypeBounds =
    import qr.*

    TypeBounds(
      TypeRepr.of[Nothing],
      kindToUpperBound(k),
    )

  def kindsToBounds(ks: Kinds)(using Quotes): List[qr.TypeBounds] =
    import qr.*

    kindsToUpperBounds(ks)
      .map(TypeBounds(TypeRepr.of[Nothing], _))

  private def kindsToUpperBounds(ks: Kinds)(using Quotes): List[qr.TypeRepr] =
    ks match
      case Kinds.Empty      => Nil
      case Kinds.Cons(h, t) => kindToUpperBound(h) :: kindsToUpperBounds(t)

  private def kindToUpperBound(k: Kind)(using Quotes): qr.TypeRepr =
    import qr.*

    k match
      case Kind.Tp =>
        TypeRepr.of[Any]
      case Kind.Arr(as, r) =>
        val bs = kindsToBounds(as)
        val t  = kindToUpperBound(r)
        TypeLambda(
          paramNames = List.range(0, bs.size).map(i => s"A$i"),
          boundsFn   = _ => bs,
          bodyFn     = _ => t,
        )
}

private class Encoding[Q <: Quotes](using val q: Q) {
  import Encoding.*
  import q.reflect.*

  class DecodingContext(stack: List[DecodingContext.Elem]) {
    import DecodingContext.*

    def substitutesType(p: ParamRef | TypeRef): Option[TypeRepr] =
      stack.collectFirst { case Elem.TypeSubstitution(src, res) if src =:= p => res }

    def substitutesTerm(i: Ident): Option[Term] =
      stack.collectFirst { case Elem.TermSubstitution(src, res) if src.termSymbol == i.symbol => res }

    def expands(p: ParamRef | TypeRef): Option[SingleOrMultiple[TypeRepr]] =
      stack.collectFirst { case Elem.TypeArgExpansion(src, res) if src =:= p => res }

    def substitutesTypeTo: TypeSubstitutionExtractor = TypeSubstitutionExtractor(this)
    def substitutesTermTo: TermSubstitutionExtractor = TermSubstitutionExtractor(this)
    def expandsTo: ExpansionExtractor = ExpansionExtractor(this)

    def push(elem: DecodingContext.Elem): DecodingContext =
      DecodingContext(elem :: stack)

    def pushAll(elems: List[DecodingContext.Elem]): DecodingContext =
      DecodingContext(elems reverse_::: stack)
  }

  object DecodingContext {
    enum Elem:
      case TypeSubstitution(src: ParamRef | TypeRef, tgt: TypeRepr)
      case TypeArgExpansion(src: ParamRef | TypeRef, tgt: SingleOrMultiple[TypeRepr])
      case TermSubstitution(src: TermRef, tgt: Term)

    class TypeSubstitutionExtractor(ctx: DecodingContext):
      def unapply(p: ParamRef | TypeRef): Option[TypeRepr] =
        ctx.substitutesType(p)

    class TermSubstitutionExtractor(ctx: DecodingContext):
      def unapply(i: Ident): Option[Term] =
        ctx.substitutesTerm(i)

    class ExpansionExtractor(ctx: DecodingContext):
      def unapply(p: ParamRef | TypeRef): Option[SingleOrMultiple[TypeRepr]] =
        ctx.expands(p)

    def empty: DecodingContext =
      DecodingContext(Nil)
  }

  case class TypeLambdaTemplate(
    paramNames: Groups[String],
    boundsFn: (tparams: Int => TypeRepr) => Groups[TypeBounds],
    bodyFn:   (tparams: Int => TypeRepr) => TypeRepr,
  ) {
    def paramNamesFlat: List[String] =
      paramNames.toFlatList

    def boundsFnFlat: (tparams: Int => TypeRepr) => List[TypeBounds] =
      boundsFn(_).toFlatList
  }

  def unsupportedType(using SourcePos, Quotes)(t: qr.TypeRepr): Nothing =
    unsupported(s"type ${typeShortCode(t)} (${qr.Printer.TypeReprStructure.show(t)})")

  def unexpectedTypeParamType(using pos: SourcePos, q: Quotes)(t: qr.TypeRepr): Nothing =
    assertionFailed(s"a type parameter that is not a ParamRef. Was ${qr.Printer.TypeReprStructure.show(t)}")

  /** Takes `Code` of the form
   *
   * ```
   * [⋅⋅[_]] =>> [A <: ⋅⋅[K], F[_ <: ⋅⋅[K]]] =>> Body[A, F]
   * ```
   *
   * and returns
   *
   * ```
   * [A..., F[...]] =>> Body[A, F]
   * ```
   */
  def decodeTypeLambda[Code <: AnyKind](using
    Type[Code],
    Reporting.Context,
  ): TypeLambdaTemplate =
    inside(TypeRepr.of[Code]) {
      TypeRepr.of[Code].dealiasKeepOpaques match
        case outer @ TypeLambda(auxNames, auxBounds, body) =>
          val List(_) = auxNames
          val List(_) = auxBounds
          val marker =
            outer.param(0) match
              case p: ParamRef => p
              case other => assertionFailed(s"Unexpected type of type lambda parameter: ${typeStruct(other)}. Expected ParamRef.")
          body match
            case inner @ TypeLambda(paramNames, paramBounds, body) =>
              val params =
                (paramNames zip paramBounds).zipWithIndex map { case ((n, b), i) =>
                  inner.param(i) match
                    case pi @ ParamRef(_, _) => (n, Left(b), pi)
                    case other => unexpectedTypeParamType(other)
                }
              val decodedTypeParams =
                decodeTypeParams(
                  marker,
                  ctx = DecodingContext.empty,
                  params
                )
              TypeLambdaTemplate(
                decodedTypeParams.decodedNames,
                boundsFn = tparams => decodedTypeParams.decodedBounds(tparams),
                bodyFn   = tparams => {
                  val ctx = decodedTypeParams.innerContext(tparams)
                  decodeType(marker, ctx, body)
                }
              )
            case other =>
              badUse(s"Expected a type lambda, got ${typeShortCode(other)}")
        case other =>
          badUse(s"Expected a type lambda, got ${typeShortCode(other)}")
    }

  def decodeParameterizedType[Code <: AnyKind, As](using
    Type[Code],
    Type[As],
  )(using
    Reporting.Context
  ): Type[Any] =
    inside(s"decoding ${typeShortCode[Code]} applied to type arguments ${typeShortCode[As]}") {
      val args = unbundleTypeArgs(Type.of[As])

      TypeRepr.of[Code].dealiasKeepOpaques match
        case outer @ TypeLambda(auxNames, auxBounds, body) =>
          val List(_) = auxNames
          val List(_) = auxBounds
          val marker = outer.param(0)
          body match
            case inner @ TypeLambda(paramNames, paramBounds, body) =>
              val params =
                (paramNames zip paramBounds).zipWithIndex map { case ((n, b), i) =>
                  inner.param(i) match
                    case pi @ ParamRef(_, _) => (n, Left(b), pi)
                    case other => unexpectedTypeParamType(other)
                }
              val substitutions =
                decodeTypeParamSubstitutions(marker, params, args.map(TypeRepr.of(using _)))
              decodeType(marker, substitutions, body)
                .asType
                .asInstanceOf[Type[Any]]
            case other =>
              badUse(s"Expected a type lambda, got ${typeShortCode(other)}")
        case other =>
          badUse(s"Expected a type lambda, got ${typeShortCode(other)}")
    }

  def decodeExpr(
    encoded: Expr[[⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any],
  )(using
    Reporting.Context,
  ): Expr[Any] =
    inside(encoded.asTerm) {
      val ParseKuotedResult(marker, kuotesParam, _, payload) =
        parseKuoted(encoded)

      decodeTerm(marker, kuotesParam.ref, ctx = DecodingContext.empty, Symbol.spliceOwner, payload)
        .asExpr
    }

  def decodeExprT[As[⋅⋅[_]]](
    encoded: Expr[[⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any],
  )(using
    Type[As],
    Reporting.Context,
  ): Expr[Any] =
    inside(encoded.asTerm) {
      val ParseKuotedResult(marker, kuotesParam, _, payload) =
        parseKuoted(encoded)

      val (userTParams, params, retTp, body) =
        doParsePolyFun(payload)

      if (params.nonEmpty)
        inside(payload) {
          badUse(s"Expected a no-value-arg function literal `[...] => () => <body>`, got a function with ${params.size} value parameter(s): ${params.map(_.name).mkString(", ")}")
        }

      val targs =
        unbundleTypeArgs(TypeRepr.of[As].appliedTo(marker).asType)
          .map(t => TypeRepr.of(using t).dealiasKeepOpaques)

      val ctx =
        decodeTypeParamSubstitutions(marker, userTParams, targs)

      decodeTerm(marker, kuotesParam.ref, ctx, Symbol.spliceOwner, body)
        .asExpr
    }

  private case class ParseKuotedResult(
    marker: TypeRef,
    kuotesParam: (name: String, tpe: TypeTree, ref: TermRef),
    retTp: TypeTree,
    body: Term,
  )

  private def parseKuoted(
    encoded: Expr[Any],
  )(using
    Reporting.Context,
  ): ParseKuotedResult =
    inside(encoded.show) {
      encoded.asTerm match
        case PolyFun(tparams, params, retTp, body) =>
          tparams match
            case tparam :: Nil =>
              val (name, kind, typeRef) = tparam
              val marker = typeRef // TODO: check that marker has kind _[_]
              params match
                case param :: Nil =>
                  ParseKuotedResult(marker, param, retTp, body)
                case _ =>
                  badUse(s"Expected a polymorphic function with 1 value parameter, but got ${params.size} value paramters")
            case Nil =>
              assertionFailed("unexpected polymorphic function with 0 type parameters")
            case tparams =>
              badUse("Expected a polymorphic function with a single type parameter [⋅⋅[_]]")
        case Inlined(call, Nil, expansion) =>
          insideInlinedCall(call):
            parseKuoted(expansion.asExpr)
        case other =>
          unsupported(s"Expected a polymorphic function `[⋅⋅[_]] => (k: Kuotes[⋅⋅]) ?=> ...`, got ${encoded.asTerm.show(using Printer.TreeStructure)}")
    }

  private case class PolyFunParseResult(
    marker: TypeRef,
    userTParams: List[(name: String, kind: Either[TypeBounds, LambdaTypeTree], ref: TypeRef)],
    params: List[(name: String, tpe: TypeTree, ref: TermRef)],
    retTp: TypeTree,
    body: Term,
  )

  private def doParsePolyFun(
    expr: Term,
  )(using
    Reporting.Context,
  ): (
    tparams: List[(name: String, kind: Either[qr.TypeBounds, qr.LambdaTypeTree], ref: qr.TypeRef)],
    params: List[(name: String, tpe: qr.TypeTree, ref: qr.TermRef)],
    retTp: qr.TypeTree,
    body: qr.Term,
  ) =
    inside(expr) {
      expr match
        case PolyFun(tparams, params, retTp, body) =>
          (tparams, params, retTp, body)
        case Inlined(call, Nil, expansion) =>
          insideInlinedCall(call):
            doParsePolyFun(expansion)
        case other =>
          badUse(s"Expected a polymorphic function, got ${expr.show(using Printer.TreeStructure)}")
    }

  private def decodeTypeParamSubstitutions(
    marker: TypeRepr,
    tparams: List[(name: String, kind: Either[TypeBounds, LambdaTypeTree], ref: ParamRef | TypeRef)],
    targs: List[TypeRepr],
  )(using
    Reporting.Context,
  ): DecodingContext = {
    import DecodingContext.Elem.{TypeSubstitution, TypeArgExpansion}

    if (tparams.size != targs.size)
      badUse(s"Expected ${targs.size} custom type parameters matching the arguments ${targs.map(t => typeShortCode(t)).mkString(", ")}. Got ${tparams.map(p => typeShortCode(p.ref)).mkString(", ")}")

    DecodingContext:
      (tparams zip targs) map {
        case ((name, bounds, ref), t) =>
          inside(s"substituting type argument ${typeShortCode(t)} for type parameter ${typeShortCode(ref)} with bounds ${bounds.fold(typeShortCode, treeShortCode)}"):
            val elem: TypeSubstitution | TypeArgExpansion =
              bounds match
                case Left(TypeBounds(lower, upper)) =>
                  upper match
                    case AppliedType(f, List(kinds)) if f =:= marker =>
                      lower.asType match
                        case '[Nothing] =>
                          decodeKindOrKinds(kinds) match
                            case Left(k) =>
                              checkKind(t, k)
                              TypeArgExpansion(ref, Single(t))
                            case Right(kinds) =>
                              val ts = unbundleTypeArgs(t.asType)
                              val ks = kinds.toList
                              if (ts.size != ks.size)
                                badUse(s"Expected ${ks.size} type arguments matching kinds ${ks.map(_.show).mkString(", ")}, got ${ts.size}: ${typeShortCode(t)}")
                              (ks zip ts).foreach { case (k, t) => checkKind(TypeRepr.of(using t), k) }
                              TypeArgExpansion(ref, Multiple(ts.map(TypeRepr.of(using _))))
                        case other =>
                          badUse(s"Cannot mix the \"spread\" upper bound (${typeShortCode(marker)}) with a lower bound (${typeShortCode(lower)})")
                    case _ =>
                      TypeSubstitution(ref, t)
                case Right(ltt) =>
                  TypeSubstitution(ref, t)

            // decode since the provided type args may contain the marker
            elem match
              case TypeSubstitution(ref, t) =>
                TypeSubstitution(ref, decodeType(marker, ctx = DecodingContext.empty, t))
              case TypeArgExpansion(ref, ts) =>
                val ts1 = ts.map(decodeType(marker, ctx = DecodingContext.empty, _))
                TypeArgExpansion(ref, ts1)
      }
  }

  private def checkKind(t: TypeRepr, k: Kind)(using Reporting.Context): Unit =
    val expectedUpperBound = kindToUpperBound(k)
    if (!(t <:< expectedUpperBound))
      badUse(s"Type ${t.show(using Printer.TypeReprShortCode)} does not have the expected kind ${k.show} (because it is not a subtype of ${expectedUpperBound.show(using Printer.TypeReprShortCode)})")

  private def decodeType(
    marker: TypeRepr,
    ctx: DecodingContext,
    body: TypeRepr,
  )(using
    Reporting.Context,
  ): TypeRepr =
    inside(body) {
      body match
        case r @ Refinement(base, memName, memType) =>
          Refinement(
            decodeType(marker, ctx, base),
            memName,
            decodeType(marker, ctx, memType),
          )
        case pt: PolyType =>
          decodePolyType(marker, ctx, pt)
        case mt: MethodType =>
          decodeMethodType(marker, ctx, mt)
        case AppliedType(f, targs) =>
          val f1 = decodeType(marker, ctx, f)
          val targs1 = expandTypeArgs(marker, ctx, targs)
            .flatMap(_.toList)
          val targs2 = targs1.map(decodeType(marker, ctx, _))
          f1.appliedTo(targs2)
        case l @ TypeLambda(names, bounds, body) =>
          val decodedTypeParams =
            decodeTypeParams(
              marker,
              ctx,
              (names zip bounds).zipWithIndex map {
                case ((n, b), i) =>
                  l.param(i) match
                    case pi: ParamRef =>
                      (n, Left(b), pi)
                    case other =>
                      unexpectedTypeParamType(other)
              }
            )
          TypeLambda(
            decodedTypeParams.decodedNamesFlat,
            tl => decodedTypeParams.decodedBoundsFlat(tl.param),
            tl => {
              val ctx1 = decodedTypeParams.innerContext(tl.param)
              decodeType(marker, ctx1, body)
            },
          )
        case t if t =:= marker =>
          // TODO: return a typed error and produce a better error message with a context of the wrongly used spread operator
          // badUse(s"Cannot use the spread operator ${typeShortCode(marker)} in this position: ${typeShortCode(body)}")
          badUse(s"Cannot use the spread operator here")
        case p: ParamRef =>
          p match
            case ctx.substitutesTypeTo(q) => q
            case ctx.expandsTo(ps)        => badUse(s"Invalid use of kind-expanded type parameter ${typeShortCode(p)} (which expands to ${ps.map(typeShortCode).mkString("(", ", ", ")")}). It can only be used in type argument position.")
            case p                        => p
        case t @ TypeRef(parent, name) =>
          t match
            case ctx.substitutesTypeTo(u) => u
            case ctx.expandsTo(ts)        => badUse(s"Invalid use of kind-expanded type parameter ${typeShortCode(t)} (which expands to ${ts.map(typeShortCode).mkString("(", ", ", ")")}). It can only be used in type argument position.")
            case t                        => checkNonOccurrence(marker, ctx, parent); t
        case TermRef(prefix, ident) =>
          TermRef(decodeType(marker, ctx, prefix), ident)
        case t: ThisType =>
          t
        case TypeBounds(lo, hi) =>
          TypeBounds(
            decodeType(marker, ctx, lo),
            decodeType(marker, ctx, hi),
          )
        case other =>
          unsupportedType(other)
    }

  private def decodeTerm(
    marker: TypeRef | ParamRef,
    kuotes: TermRef,
    ctx: DecodingContext,
    owner: Symbol,
    expr: Term,
  )(using
    Reporting.Context,
  ): Term =
    inside(expr) {
      expr match
        // '{ kuotes.splice[T](arg)[U] }
        case TypeApply(Apply(TypeApply(Select(prefix, "splice"), List(t)), List(arg)), List(u)) if prefix.tpe == kuotes =>
          // check that arg :《u》, ensuring that arg is usable in place where 《u》 is expected
          val decodedU =
            decodeType(marker, ctx, u.tpe)
          val decodedUType =
            decodedU.asType.asInstanceOf[Type[Any]]
          if (arg.asExpr.isExprOf(using decodedUType))
            arg.changeOwner(owner).asExprOf(using decodedUType).asTerm
          else
            given Printer[Tree] = Printer.TreeShortCode
            given Printer[TypeRepr] = Printer.TypeReprShortCode
            badUse(s"Got ${arg.show} of type ${t.show}, expected type ${decodedU.show} (which is the decoding of ${u.show})")
        case PolyFun(tparams, params, retTp, body) =>
          decodePolyFun(marker, kuotes, ctx, tparams, params, retTp, body, owner)
        case bl @ Block(List(stmt), Closure(method, optTp)) =>
          (stmt, method) match
            case (DefDef(name, paramss, retTp, Some(body)), Ident(methodName)) if methodName == name =>
              paramss match
                case TermParamClause(params) :: Nil => Symbol.noSymbol.termRef
                  decodeFun(
                    marker,
                    kuotes,
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
        case Block(stmts, term) =>
          decodeBlock(marker, kuotes, ctx, owner, stmts, term)
        case Apply(f, as) =>
          val f1 = decodeTerm(marker, kuotes, ctx, owner, f)
          val bs = as.map(decodeTerm(marker, kuotes, ctx, owner, _))
          Apply(f1, bs)
        case TypeApply(f, ts) =>
          val f1 = decodeTerm(marker, kuotes, ctx, owner, f)
          val ts1 = expandTypeArgs(marker, ctx, ts.map(_.tpe))
            .flatMap(_.toList)
          val ts2 = ts1.map(decodeType(marker, ctx, _))
          TypeApply(f1, ts2.map(t => TypeTree.of(using t.asType)))
        case Select(prefix, name) =>
          val prefix1 = decodeTerm(marker, kuotes, ctx, owner, prefix)
          try {
            Select.unique(prefix1, name)
          } catch {
            e => unsupported(s"x.$name for overloaded method $name. In ${treeShortCode(prefix1)}.$name")
          }
        case Typed(x, t) =>
          Typed(
            decodeTerm(marker, kuotes, ctx, owner, x),
            TypeTree.of(using
              decodeType(marker, ctx, t.tpe).asType
            ),
          )
        case New(tt) =>
          New(TypeTree.of(using decodeType(marker, ctx, tt.tpe).asType))
        case i @ Ident(x) =>
          i match
            case ctx.substitutesTermTo(j) => j
            case i => i
        case l: Literal =>
          l
        case Repeated(as, tt) =>
          Repeated(
            as.map { a => decodeTerm(marker, kuotes, ctx, owner, a) },
            TypeTree.of(using decodeType(marker, ctx, tt.tpe).asType),
          )
        case Inlined(call, bindings, expansion) =>
          Inlined(
            call,
            bindings,
            insideInlinedCall(call) {
              decodeTerm(marker, kuotes, ctx, owner, expansion)
            },
          ).changeOwner(owner)
        case other =>
          unimplemented(s"decodeTerm(${treeStruct(expr)})")
    }

  private def decodeBlock(
    marker: TypeRef | ParamRef,
    kuotes: TermRef,
    ctx: DecodingContext,
    owner: Symbol,
    stmts: List[Statement],
    expr: Term,
  )(using
    Reporting.Context,
  ): Block = {
    val (ctx1, stmtFns) =
      stmts.mapS[DecodingContext, (fullCtx: DecodingContext) => Statement](ctx) {
        (ctx, stmt) =>
          inside(stmt) {
            stmt match
              case defn: Definition =>
                val (ctxElem, stmtFn) = decodeDefinition(marker, kuotes, ctx, owner, defn)
                (ctx.push(ctxElem), stmtFn)
              case other =>
                unimplemented(s"decoding statement ${treeShortCode(other)}\nTree: ${treeStruct(other)}")
          }
      }
    val stmts1 = stmtFns.map(_(ctx1))
    Block(stmts1, decodeTerm(marker, kuotes, ctx1, owner, expr))
  }

  private def decodeDefinition(
    marker: TypeRef | ParamRef,
    kuotes: TermRef,
    ctx: DecodingContext,
    owner: Symbol,
    defn: Definition,
  )(using
    Reporting.Context,
  ): (DecodingContext.Elem, (fullCtx: DecodingContext) => Statement) = {
    defn match
      case v @ ValDef(name, tpt, Some(body)) =>
        val oldRef = v.symbol.termRef
        val newTpe = decodeType(marker, ctx, tpt.tpe)
        val flags = v.symbol.flags
        val newSym = Symbol.newVal(
          owner,
          name,
          newTpe,
          // v.symbol.flags,  // throws an error (https://github.com/scala/scala3/issues/25412)
          Flags.EmptyFlags,
          privateWithin = Symbol.noSymbol,
        )
        ( DecodingContext.Elem.TermSubstitution(oldRef,  Ref.term(newSym.termRef))
        , ctx => ValDef(newSym, Some(decodeTerm(marker, kuotes, ctx, owner = newSym, body)))
        )
      case other =>
        unimplemented(s"decoding definition ${treeShortCode(other)}\nTree: ${treeStruct(other)}")
  }

  private def decodePolyType(
    marker: TypeRepr,
    ctx: DecodingContext,
    pt: PolyType,
  )(using
    Reporting.Context,
  ): PolyType =
    val PolyType(tParamNames, tParamBounds, body) = pt

    val decodedTypeParams =
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

    PolyType(decodedTypeParams.decodedNamesFlat)(
      pt => decodedTypeParams.decodedBoundsFlat(pt.param),
      pt => {
        val ctx1 = decodedTypeParams.innerContext(pt.param)
        decodeType(marker, ctx1, body)
      },
    )

  private def decodeMethodType(
    marker: TypeRepr,
    ctx: DecodingContext,
    methType: MethodType,
  )(using
    Reporting.Context,
  ): MethodType =
    val MethodType(paramNames, paramTypes, returnType) = methType
    MethodType(paramNames)(
      _ => paramTypes.map(t => decodeType(marker, ctx, t)),
      _ => decodeType(marker, ctx, returnType)
    )

  private def decodePolyFun(
    marker: TypeRef | ParamRef,
    kuotes: TermRef,
    ctx: DecodingContext,
    tparams: List[(name: String, kind: Either[TypeBounds, LambdaTypeTree], ref: TypeRef)],
    params: List[(name: String, tpe: TypeTree, ref: TermRef)],
    returnType: TypeTree,
    body: Term,
    owner: Symbol,
  )(using
    Reporting.Context,
  ): Term = {
    val decodedTypeParams =
      decodeTypeParams(marker, ctx, tparams)

    def tParamBounds1(tparams: Int => TypeRepr): List[TypeBounds] =
      decodedTypeParams.decodedBoundsFlat(tparams)

    val paramNames = params.map(_.name)

    def paramTypes(tparams: Int => TypeRepr): List[TypeRepr] =
      val ctx1 = decodedTypeParams.innerContext(tparams)
      params.map(t => decodeType(marker, ctx1, t.tpe.tpe))

    def returnType1(tparams: Int => TypeRepr): TypeRepr =
      val ctx1 = decodedTypeParams.innerContext(tparams)
      decodeType(marker, ctx1, returnType.tpe)

    def paramSubstitutions(newParams: List[Term]): List[DecodingContext.Elem.TermSubstitution] =
      (params zip newParams).map { case (pOld, pNew) =>
        DecodingContext.Elem.TermSubstitution(pOld.ref, pNew)
      }

    def body1(newTParams: Int => TypeRepr, newParams: List[Term], owner: Symbol): Term =
      val ctx1 = decodedTypeParams.innerContext(newTParams)
      val ctx2 = ctx1.pushAll(paramSubstitutions(newParams))
      decodeTerm(marker, kuotes, ctx2, owner, body)

    PolyFun(decodedTypeParams.decodedNamesFlat, tParamBounds1, paramNames, paramTypes, returnType1, body1, owner)
  }

  private def decodeFun(
    marker: TypeRef | ParamRef,
    kuotes: TermRef,
    ctx: DecodingContext,
    params: List[(name: String, tpe: TypeTree, ref: TermRef)],
    returnType: TypeTree,
    body: Term,
    owner: Symbol,
  )(using
    Reporting.Context,
  ): Term = {

    val paramNames = params.map(_.name)

    val paramTypes =
      params.map(t => decodeType(marker, ctx, t.tpe.tpe))

    val returnType1: TypeRepr =
      decodeType(marker, ctx, returnType.tpe)

    def paramSubstitutions(newParams: List[Term]): List[DecodingContext.Elem.TermSubstitution] =
      (params zip newParams).map { case (pOld, pNew) =>
        DecodingContext.Elem.TermSubstitution(pOld.ref, pNew)
      }

    def body1(newParams: List[Term], owner: Symbol): Term =
      val ctx1 = ctx.pushAll(paramSubstitutions(newParams))
      decodeTerm(marker, kuotes, ctx1, owner, body)

    Lambda(
      owner = owner,
      tpe = MethodType(paramNames)(_ => paramTypes, _ => returnType1),
      rhsFn = (sym, argTrees) => {
        val args = argTrees.map(_.asInstanceOf[Term])
        body1(args, sym)
      },
    )
  }

  private def decodeTypeParams(
    marker: TypeRepr,
    ctx: DecodingContext,
    tParams: List[(name: String, kind: Either[TypeBounds, LambdaTypeTree], ref: ParamRef | TypeRef)],
  )(using
    Reporting.Context,
  ): DecodedTypeParams = {
    def expandParam(name: String, kinds: TypeRepr)(using Reporting.Context): SingleOrMultiple[(String, Kind)] =
      decodeKindOrKinds(kinds) match
        case Left(kind)   => Single((name, kind))
        case Right(kinds) => Multiple(
          kinds
            .toList
            .zipWithIndex
            .map { case (bounds, i) => (name + "$" + i, bounds) }
        )

    val expandedTParams: List[PostExpansionParam] =
      inside("TODO: refine (bjao)") {
        tParams.map:
          case (name, Left(bounds @ TypeBounds(lower, AppliedType(f, List(kinds)))), origParam) if f =:= marker =>
            lower.asType match
              case '[Nothing] =>
                val expanded = expandParam(name, kinds)
                PostExpansionParam.Expanded(expanded, origParam)
              case other =>
                badUse(s"Cannot mix the \"spread\" upper bound (${typeShortCode(marker)}) with a lower bound (${typeShortCode(lower)})")
          case (name, kind, origParam) =>
            PostExpansionParam.Original(name, kind, origParam)
      }

    DecodedTypeParams(marker, ctx, expandedTParams)
  }

  private enum PostExpansionParam:
    case Original(name: String, kind: Either[TypeBounds, LambdaTypeTree], ref: ParamRef | TypeRef)
    case Expanded(params: SingleOrMultiple[(String, Kind)], originalParamRef: ParamRef | TypeRef)

    def expandedSize: Int =
      this match
        case Original(_, _, _) => 1
        case Expanded(ps, _) => ps.size

  private class DecodedTypeParams(
    marker: TypeRepr,
    ctx: DecodingContext,
    expandedTypeParams: List[(index: Int, expanded: PostExpansionParam)],
  ) {
    private lazy val names0: Groups[String] =
      Groups.fromList:
        expandedTypeParams.map:
          case (_, PostExpansionParam.Original(name, _, _))         => Single(name)
          case (_, PostExpansionParam.Expanded(Single((n, _)), _))  => Single(n)
          case (_, PostExpansionParam.Expanded(Multiple(ps), _))    => Multiple(ps.map { case (n, _) => n })

    private lazy val bounds0: Groups[Either[q.reflect.TypeBounds, q.reflect.LambdaTypeTree]] =
      Groups.fromList:
        expandedTypeParams.map:
          case (_, PostExpansionParam.Original(_, bounds, _))       => Single(bounds)
          case (_, PostExpansionParam.Expanded(Single((_, k)), _))  => Single(Left(kindToBounds(k)))
          case (_, PostExpansionParam.Expanded(Multiple(ps), _))    => Multiple(ps.map { case (_, k) => Left(kindToBounds(k)) })

    def decodedNames: Groups[String] =
      names0

    def decodedNamesFlat: List[String] =
      decodedNames.toFlatList

    def innerContext(actualTypeParams: Int => TypeRepr): DecodingContext =
      val newSubstitutions: List[DecodingContext.Elem] =
        expandedTypeParams
          .map {
            case (j, PostExpansionParam.Expanded(ps, origRef)) =>
              DecodingContext.Elem.TypeArgExpansion(origRef, ps.zipWithIndex.map { case (_, i) => actualTypeParams(j + i) })
            case (j, PostExpansionParam.Original(_, _, origRef)) =>
              DecodingContext.Elem.TypeSubstitution(origRef, actualTypeParams(j))
          }
      ctx.pushAll(newSubstitutions)

    def decodedBoundsAndInnerContext(
      actualTypeParams: Int => TypeRepr,
    )(using
      Reporting.Context,
    ): (bounds: Groups[TypeBounds], innerContext: DecodingContext) =
      val ctx1 = innerContext(actualTypeParams)
      val bounds1 = bounds0.map(decodeTypeBounds(marker, ctx1, _))
      (bounds1, ctx1)

    def decodedBounds(
      actualTypeParams: Int => TypeRepr,
    )(using
      Reporting.Context,
    ): Groups[TypeBounds] =
      decodedBoundsAndInnerContext(actualTypeParams).bounds

    def decodedBoundsFlat(
      actualTypeParams: Int => TypeRepr,
    )(using
      Reporting.Context,
    ): List[TypeBounds] =
      decodedBounds(actualTypeParams)
        .toFlatList
  }

  private object DecodedTypeParams {
    def apply(
      marker: TypeRepr,
      ctx: DecodingContext,
      expandedTypeParams: List[PostExpansionParam],
    ): DecodedTypeParams =
      val expandedTypeParamsWithIndex: List[(Int, PostExpansionParam)] =
        expandedTypeParams
          .mapS(0) { (j, p) => (j + p.expandedSize, (j, p)) }
          ._2
      new DecodedTypeParams(marker, ctx, expandedTypeParamsWithIndex)
  }

  private def expandTypeArgs(
    marker: TypeRepr,
    ctx: DecodingContext,
    targs: List[TypeRepr],
  )(using
    Reporting.Context,
  ): List[SingleOrMultiple[TypeRepr]] =
    targs.map { ta =>
      inside(ta) {
        ta match {
          case fa @ AppliedType(f, targs) =>
            if (f =:= marker) {
              // encode the expanded argument (A --> A1, ...) into a single type A1 :: ...
              val m = typeShortCode(marker)
              targs match
                case a :: Nil =>
                  val a1: ParamRef | TypeRef = a match
                    case a: ParamRef => a
                    case a: TypeRef  => a
                    case a           => badUse(s"Invalid application of $m in ${typeShortCode(fa)}. Spread operator $m can only be applied to type parameters.")
                  a1 match
                    case ctx.expandsTo(as) =>
                      as match
                        case Single(a) => Single(a)
                        case Multiple(as) => Single(bundleTypeArgs(as))
                    case a1 =>
                      badUse(s"Invalid application of $m in ${typeShortCode(fa)}. ${typeShortCode(a1)} is not <: $m[<kinds>]")
                case other =>
                  assertionFailed(s"Expected 1 type argument to ${typeShortCode(f)}, got ${targs.size} (${targs.map(typeShortCode).mkString(", ")})")
            } else {
              Single(fa)
            }
          case p: ParamRef =>
            p match
              case ctx.expandsTo(ps) => ps
              case _                 => Single(p)
          case t: TypeRef =>
            t match
              case ctx.expandsTo(ts) => ts
              case _                 => Single(t)
          case other =>
            Single(other)
        }
      }
    }

  private def decodeTypeBounds(
    marker: TypeRepr,
    ctx: DecodingContext,
    bounds: Either[TypeBounds, LambdaTypeTree],
  )(using
    Reporting.Context,
  ): TypeBounds =
    bounds match
      case Left(tb @ TypeBounds(lo, hi)) =>
        inside(tb):
          TypeBounds(
            decodeType(marker, ctx, lo),
            decodeType(marker, ctx, hi),
          )
      case Right(ltt @ LambdaTypeTree(typeDefs, body)) =>
        inside(ltt) {
          val bodyTpe: Either[TypeRepr, LambdaTypeTree] =
            body match
              case tb: TypeBoundsTree =>
                val TypeBounds(lo, hi) = tb.tpe
                lo.asType match
                  case '[Nothing] => Left(hi)
                  case _ => assertionFailed(s"Unexpected lower bound on the body of LambdaTypeTree: ${typeStruct(lo)}")
              case lt: LambdaTypeTree => Right(lt)
              case other => assertionFailed(s"Unexpected body of LambdaTypeTree in bounds position: ${treeStruct(other)}. Expected TypeBoundsTree or LambdaTypeTree.")
          val decodedTypeParams =
            decodeTypeParams(
              marker,
              ctx,
              typeDefs map { case td @ TypeDef(name, tree) =>
                tree match
                  case b: TypeBoundsTree => (name, Left(b.tpe), td.symbol.typeRef)
                  case l: LambdaTypeTree => (name, Right(l),    td.symbol.typeRef)
                  case other =>
                    assertionFailed(s"Unexpected ${treeStruct(other)} as the type/kind of a type param")
              },
            )
          TypeBounds(
            low = TypeRepr.of[Nothing],
            hi  = TypeLambda(
              decodedTypeParams.decodedNamesFlat,
              tl => decodedTypeParams.decodedBoundsFlat(tl.param),
              tl => {
                val ctx1 = decodedTypeParams.innerContext(tl.param)
                bodyTpe match
                  case Left(t)    => decodeType(marker, ctx1, t)
                  case Right(ltt) => decodeTypeBounds(marker, ctx1, Right(ltt))
              }
            ),
          )
        }

  private def checkNonOccurrence(
    marker: TypeRepr,
    ctx: DecodingContext,
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
