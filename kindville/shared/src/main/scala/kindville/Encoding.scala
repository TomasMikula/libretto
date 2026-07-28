package kindville

import kindville.Reporting.*
import kindville.SingleOrMultiple.{Multiple, Single}
import scala.quoted.*
import scala.util.chaining.*

private object Encoding {
  def apply(using q: Quotes)(): Encoding[q.type] =
    new Encoding[q.type]

  private def provided[A](a: A)[B](f: A ?=> B): B =
    f(using a)

  extension [A](as: List[A]) {
    def mapS[S, B](s: S)(f: (S, A) => (S, B)): (S, List[B]) =
      as match
        case Nil =>
          (s, Nil)
        case a :: as =>
          val (s1, b) = f(s, a)
          val (s2, bs) = as.mapS(s1)(f)
          (s2, b :: bs)

    def getSingle(otherwise: => A): A =
      as match
        case a :: Nil => a
        case _ => otherwise
  }

  def bundleTypeArgs(using Quotes)(args: List[qr.TypeRepr]): qr.TypeRepr =
    import quotes.reflect.*
    args match
      case Nil => TypeRepr.of[TNil]
      case t :: ts => TypeRepr.of[::].appliedTo(List(t, bundleTypeArgs(ts)))

  def bundleTypeArgs(using Quotes)(args: SingleOrMultiple[qr.TypeRepr]): qr.TypeRepr =
    args match
      case Single(a) => a
      case Multiple(as) => bundleTypeArgs(as)

  def unbundleTypeArgs(using Quotes)(args: qr.TypeRepr): Either[String, List[qr.TypeRepr]] =
    import quotes.reflect.*

    val cons = TypeRepr.of[::]

    args match
      case t if t =:= TypeRepr.of[TNil] =>
        Right(Nil)
      case AppliedType(f, args) =>
        f.asType match
          case '[::] =>
            args match
              case h :: t :: Nil =>
                unbundleTypeArgs(t)
                  .map(h :: _)
              case _ =>
                assertionFailed(s"Unexpected number of type arguments to ${typeShortCode(f)}. Expected 2, got ${args.size}: ${args.map(typeShortCode(_)).mkString(", ")}")
          case _ =>
            Left(s"${typeShortCode(f)} is neither ${typeShortCode[TNil]} nor ${typeShortCode[::]}")
      case other =>
        Left(s"${typeShortCode(other)} is neither ${typeShortCode[TNil]} nor ${typeShortCode[::]}")

  def unbundleTypeArgsOrFail(using Quotes, Reporting.Context)(args: qr.TypeRepr): List[qr.TypeRepr] =
    unbundleTypeArgs(args) match
      case Right(res) => res
      case Left(msg) => badUse(s"Cannot decode a list of type arguments from type ${typeShortCode(args)}: $msg")


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

    def expands(p: ParamRef | TypeRef): Option[ParamExpansion] =
      stack.collectFirst {
        case Elem.TypeArgExpansion(src, res) if src =:= p => ParamExpansion.StaticallyKnown(res)
        case Elem.TypeArgForgedExpansion(src, bundled, ks) if src =:= p => ParamExpansion.Forged(bundled, ks)
      }

    def substitutesTypeTo: TypeSubstitutionExtractor = TypeSubstitutionExtractor(this)
    def substitutesTermTo: TermSubstitutionExtractor = TermSubstitutionExtractor(this)
    def expandsTo: ExpansionExtractor = ExpansionExtractor(this)

    def push(elem: DecodingContext.Elem): DecodingContext =
      DecodingContext(elem :: stack)

    def pushAll(elems: List[DecodingContext.Elem]): DecodingContext =
      DecodingContext(elems reverse_::: stack)

    override def toString: String =
      stack.reverse.mkString("\n")
  }

  object DecodingContext {
    enum Elem:
      case TypeSubstitution(src: ParamRef | TypeRef, tgt: TypeRepr)
      case TypeArgExpansion(src: ParamRef | TypeRef, tgt: SingleOrMultiple[TypeRepr])
      case TypeArgForgedExpansion(src: ParamRef | TypeRef, bundledArg: TypeRepr, kind: SingleOrMultiple[Kind])
      case TermSubstitution(src: TermRef, tgt: Term)

    class TypeSubstitutionExtractor(ctx: DecodingContext):
      def unapply(p: ParamRef | TypeRef): Option[TypeRepr] =
        ctx.substitutesType(p)

    class TermSubstitutionExtractor(ctx: DecodingContext):
      def unapply(i: Ident): Option[Term] =
        ctx.substitutesTerm(i)

    class ExpansionExtractor(ctx: DecodingContext):
      def unapply(p: ParamRef | TypeRef): Option[ParamExpansion] =
        ctx.expands(p)

    enum ParamExpansion:
      case StaticallyKnown(unbundled: SingleOrMultiple[TypeRepr])
      case Forged(bundledArg: TypeRepr, kinds: SingleOrMultiple[Kind])

      def bundled(forceExplicitBundle: Boolean): TypeRepr =
        this match
          case StaticallyKnown(unbundled) =>
            bundleTypeArgs(unbundled)
          case Forged(bundledArg, kinds) =>
            if (forceExplicitBundle)
              bundleTypeArgs(kinds `map` kindToUpperBound)
            else
              bundledArg

    def empty: DecodingContext =
      DecodingContext(Nil)
  }

  object ParamRefOrTypeRef {
    def unapply(t: TypeRepr): Option[ParamRef | TypeRef] =
      t match
        case ref: ParamRef => Some(ref)
        case ref: TypeRef => Some(ref)
        case _ => None
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
                  localMarker = None,
                  ctx = DecodingContext.empty,
                  params
                )
              TypeLambdaTemplate(
                decodedTypeParams.decodedNames,
                boundsFn = tparams => decodedTypeParams.decodedBounds(tparams),
                bodyFn   = tparams => {
                  val ctx = decodedTypeParams.innerContext(tparams)
                  decodeType(marker, localMarker = None, ctx, body)
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
    decodeParameterizedType(TypeRepr.of[Code], TypeRepr.of[As])
      .asType
      .asInstanceOf[Type[Any]]

  def decodeParameterizedType(
    code: TypeRepr,
    bundledArgs: TypeRepr,
  )(using
    Reporting.Context
  ): TypeRepr =
    inside(s"decoding ${typeShortCode(code)} applied to type arguments ${typeShortCode(bundledArgs)}") {
      val args = unbundleTypeArgsOrFail(bundledArgs)

      code.dealiasKeepOpaques match
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
                decodeTypeParamSubstitutions(marker, params, args,
                  considering = Seq.empty, // XXX: might lead to confusing error message, namely invalid suggestion to provide ofKinds witness explicitly
                )
              decodeType(marker, localMarker = None, substitutions, body)
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

      decodeTerm(marker, kuotesParam.ref, localMarker = None, rekindle = None, ctx = DecodingContext.empty, Symbol.spliceOwner, payload)
        .asExpr
    }

  def decodeExprT[As[⋅⋅[_]]](
    encoded: Expr[[⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any],
    considering: Seq[Expr[? ofKinds ?]],
  )(using
    Type[As],
    Reporting.Context,
  ): Expr[Any] =
    inside(encoded.asTerm) {
      val ParseKuotedResult(marker, kuotesParam, _, payload) =
        parseKuoted(encoded)

      val (userTParams, params, paramsGiven, retTp, body) =
        doParsePolyFun(payload)

      if (params.nonEmpty)
        inside(payload) {
          badUse(s"Expected a no-value-arg function literal `[...] => () => <body>`, got a function with ${params.size} value parameter(s): ${params.map(_.name).mkString(", ")}")
        }

      val targs =
        unbundleTypeArgsOrFail(TypeRepr.of[As].appliedTo(marker))
          .map(_.dealiasKeepOpaques)

      val ctx =
        decodeTypeParamSubstitutions(marker, userTParams, targs, considering)

      decodeTerm(marker, kuotesParam.ref, localMarker = None, rekindle = None, ctx, Symbol.spliceOwner, body)
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
        case PolyFun(tparams, params, paramsGiven, retTp, body) =>
          val tparam = tparams.getSingle(otherwise = badUse("Expected a polymorphic function with a *single* type parameter [⋅⋅[_]]"))
          val (name, kind, typeRef) = tparam
          val marker = typeRef // TODO: check that marker has kind _[_]
          val param = params.getSingle(otherwise = badUse(s"Expected a polymorphic function with 1 given value parameter, but got ${params.size} value paramters"))
          if (paramsGiven)
            ParseKuotedResult(marker, param, retTp, body)
          else
            badUse(s"Expected a polymorphic function with a given value parameter, but ${param.name} is not given")
        case Inlined(call, Nil, expansion) =>
          insideInlinedCall(call):
            parseKuoted(expansion.asExpr)
        case other =>
          unsupported(s"Expected a polymorphic function `[⋅⋅[_]] => (k: Kuotes[⋅⋅]) ?=> ...`, got ${encoded.asTerm.show(using Printer.TreeStructure)}")
    }

  private case class ParsedRekindleArg(
    marker: TypeRef,
    rekindle: (name: String, tpe: TypeTree, ref: TermRef), // Kuotes.Rekindle[⋅⋅, ⋅⋅⋅]
    retTp: TypeTree,
    body: Term,
  )

  private def parseRekindleArg(
    f: Term,
  )(using
    Reporting.Context,
  ): ParsedRekindleArg =
    inside(treeShortCode(f)) {
      f match
        case PolyFun(tparams, params, paramsGiven, retTp, body) =>
          val (_, _, localMarker) =
            tparams.getSingle(otherwise = badUse(s"Expected a polymorphic function with 1 type parameter, but got ${tparams.size}"))
          val rekindle =
            params.getSingle(otherwise = badUse(s"Expected a polymorphic function with 1 given value parameter, but got ${params.size} value paramters"))
          if (!paramsGiven)
            badUse(s"Expected a polymorphic function with a given value parameter, but ${rekindle.name} is not given")
          ParsedRekindleArg(localMarker, rekindle, retTp, body)
        case Inlined(call, Nil, expansion) =>
          insideInlinedCall(call):
            parseRekindleArg(expansion)
        case other =>
          unsupported(s"Expected a polymorphic function `[⋅⋅⋅[_]] => (ev: Kuotes.Rekindle[⋅⋅, ⋅⋅⋅]) ?=> ...`, got ${treeStruct(f)}")
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
    paramsGiven: Boolean,
    retTp: qr.TypeTree,
    body: qr.Term,
  ) =
    inside(expr) {
      expr match
        case PolyFun(tparams, params, paramsGiven, retTp, body) =>
          (tparams, params, paramsGiven, retTp, body)
        case Inlined(call, Nil, expansion) =>
          insideInlinedCall(call):
            doParsePolyFun(expansion)
        case other =>
          badUse(s"Expected a polymorphic function with a single type parameter list, got ${expr.show(using Printer.TreeStructure)}")
    }

  private def decodeTypeParamSubstitutions(
    marker: TypeRepr,
    tparams: List[(name: String, kind: Either[TypeBounds, LambdaTypeTree], ref: ParamRef | TypeRef)],
    targs: List[TypeRepr],
    considering: Seq[Expr[? ofKinds ?]], // explicitly provided kind witnesses for consideration; workaround for https://github.com/scala/scala3/issues/26589
  )(using
    Reporting.Context,
  ): DecodingContext = {
    import DecodingContext.Elem.{TypeSubstitution, TypeArgExpansion, TypeArgForgedExpansion}

    if (tparams.size != targs.size)
      badUse(s"Expected ${targs.size} custom type parameters matching the arguments ${targs.map(t => typeShortCode(t)).mkString(", ")}. Got ${tparams.map(p => typeShortCode(p.ref)).mkString(", ")}")

    DecodingContext:
      (tparams zip targs) map {
        case ((name, bounds, ref), t) =>
          inside(s"substituting type argument ${typeShortCode(t)} for type parameter ${typeShortCode(ref)} with bounds ${bounds.fold(typeShortCode, treeShortCode)}"):
            val elem: TypeSubstitution | TypeArgExpansion | TypeArgForgedExpansion =
              bounds match
                case Left(TypeBounds(lower, upper)) =>
                  upper match
                    case AppliedType(f, List(kinds)) if f =:= marker =>
                      lower.asType match
                        case '[Nothing] =>
                          matchArgAgainstKinds(ref, kinds, t, considering)
                        case other =>
                          badUse(s"Cannot mix the \"spread\" upper bound (${typeShortCode(marker)}) with a lower bound (${typeShortCode(lower)})")
                    case _ =>
                      TypeSubstitution(ref, t)
                case Right(ltt) =>
                  TypeSubstitution(ref, t)

            // decode since the provided type args may contain the marker
            elem match
              case TypeSubstitution(ref, t) =>
                TypeSubstitution(ref, decodeType(marker, localMarker = None, ctx = DecodingContext.empty, t))
              case TypeArgExpansion(ref, ts) =>
                // TODO: Why? Shouldn't type argument be free of the marker, since it's provided outside of marker's scope?
                val ts1 = ts.map(decodeType(marker, localMarker = None, DecodingContext.empty, _))
                TypeArgExpansion(ref, ts1)
              case x: TypeArgForgedExpansion =>
                x
      }
  }

  private def matchArgAgainstKinds(
    formalTParam: ParamRef | TypeRef,
    kinds: TypeRepr,
    tArg: TypeRepr,
    considering: Seq[Expr[? ofKinds ?]], // explicitly provided kind witnesses for consideration; workaround for https://github.com/scala/scala3/issues/26589
  )(using
    Reporting.Context,
  ): DecodingContext.Elem.TypeArgExpansion | DecodingContext.Elem.TypeArgForgedExpansion = {
    import DecodingContext.Elem.{TypeArgExpansion, TypeArgForgedExpansion}

    val decodedKinds: SingleOrMultiple[Kind] =
      decodeKindOrKinds(kinds) match
        case Left(k) => Single(k)
        case Right(ks) => Multiple(ks.toList)

    val alignedArgsToKinds: Either[String, SingleOrMultiple[(Kind, TypeRepr)]] =
      decodedKinds match
        case Single(k) =>
          Right(Single((k, tArg)))
        case Multiple(ks) =>
          unbundleTypeArgs(tArg) match
            case Left(reason) =>
              Left(s"Cannot prove that ${typeShortCode(tArg)} is a list of types, because $reason")
            case Right(ts) =>
              if (ts.size != ks.size)
                // fatal, fail without looking for ofKinds evidence
                badUse(s"Expected ${ks.size} type arguments matching kinds ${ks.map(_.show).mkString(", ")}, got ${ts.size}: ${typeShortCode(tArg)}")
              Right(Multiple(ks zip ts))

    val kindCheckedArgs: Either[String, SingleOrMultiple[TypeRepr]] =
      alignedArgsToKinds.flatMap(_.traverse {
        case (k, t) =>
          val expectedUpperBound = kindToUpperBound(k)
          if (t <:< expectedUpperBound)
            Right(t)
          else
            Left(s"Type ${typeShortCode(t)} does not have the expected kind ${k.show} (because it is not a subtype of ${typeShortCode(expectedUpperBound)})")
      })

    kindCheckedArgs match
      case Right(ts) =>
        TypeArgExpansion(formalTParam, ts)
      case Left(msg) =>
        val tOfKindsK = TypeRepr.of[ofKinds].appliedTo(List(tArg, kinds))
        Implicits.search(tOfKindsK) match
          case iss: ImplicitSearchSuccess =>
            TypeArgForgedExpansion(formalTParam, bundledArg = tArg, decodedKinds)
          case e: NoMatchingImplicits =>
            badUse(s"No matching implicits for ${typeShortCode(tOfKindsK)}:\n${e.explanation}")
          case e: AmbiguousImplicits =>
            badUse(s"Ambiguous implicits for ${typeShortCode(tOfKindsK)}:\n${e.explanation}")
          case e: DivergingImplicit =>
            badUse(s"Diverging implicit search for ${typeShortCode(tOfKindsK)}:\n${e.explanation}")
          case e: ImplicitSearchFailure =>
            if (considering.exists(_.isExprOf(using tOfKindsK.asType.asInstanceOf[Type[Any]])))
              TypeArgForgedExpansion(formalTParam, bundledArg = tArg, decodedKinds)
            else
              badUse:
                s"""Cannot prove that type ${typeShortCode(tArg)} has the expected kind ${decodedKinds.map(_.show).mkString("", " :: ", " :: TNil")}, because
                    | - $msg,
                    | - nor is there an instance of ${typeShortCode(tOfKindsK)} among the ${considering.size} instances provided explicitly to the decoding macro
                    | - nor is there a given instance of ${typeShortCode(tOfKindsK)} in scope
                    |   - although this could be a false negative due to https://github.com/scala/scala3/issues/26589,
                    |     in which case work around it by passing an explicit instance to the decode macro
                    |   - reported explanation:
                    |     ${e.explanation.replace("\n", "\n     ")}
                    |""".stripMargin
  }

  def compiletimeKindCheck[A <: AnyKind, K](using Type[A], Type[K], Reporting.Context): Expr[Unit] =
    decodeKindOrKinds(TypeRepr.of[K]) match
      case Left(k) =>
        val expectedUpperBound = kindToUpperBound(k)
        if (TypeRepr.of[A] <:< expectedUpperBound)
          '{ () }
        else
          badUse(s"${typeShortCode[A]} is not statically known to be of kind ${k.show}, because it is not a subtype of ${{typeShortCode(expectedUpperBound)}}")
      case Right(ks) =>
        unimplemented("Multi-kind compiletimeKindCheck")

  private def decodeType(
    marker: TypeRepr,
    localMarker: Option[TypeRef],
    ctx: DecodingContext,
    body: TypeRepr,
  )(using
    Reporting.Context,
  ): TypeRepr =
    inside(body) {
      body match
        case r @ Refinement(base, memName, memType) =>
          Refinement(
            decodeType(marker, localMarker, ctx, base),
            memName,
            decodeType(marker, localMarker, ctx, memType),
          )
        case pt: PolyType =>
          decodePolyType(marker, localMarker, ctx, pt)
        case mt: MethodType =>
          decodeMethodType(marker, localMarker, ctx, mt)
        case AppliedType(f, targs) =>
          if (f =:= marker)
            expandAndBundleTypeArg(marker, ctx, targs, forceExplicitBundle = false)
          else if (localMarker.exists(f =:= _))
            expandAndBundleTypeArg(localMarker.get, ctx, targs, forceExplicitBundle = true)
          else
            val f1 = decodeType(marker, localMarker, ctx, f)
            val targs1 = expandTypeArgs(marker, localMarker, ctx, targs)
              .flatMap(_.toList)
            val targs2 = targs1.map(decodeType(marker, localMarker, ctx, _))
            f1.appliedTo(targs2)
        case l @ TypeLambda(names, bounds, body) =>
          val decodedTypeParams =
            decodeTypeParams(
              marker,
              localMarker,
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
              decodeType(marker, localMarker, ctx1, body)
            },
          )
        case t if t =:= marker =>
          badUse(s"Cannot use the spread operator here")
        case t if localMarker.exists(_ =:= t) =>
          badUse(s"Cannot use the local spread operator here")
        case ParamRefOrTypeRef(ref) =>
          ref match
            case ctx.substitutesTypeTo(q) => q
            case ctx.expandsTo(x) =>
              import DecodingContext.ParamExpansion
              val expansionMsg = x match
                case ParamExpansion.StaticallyKnown(ts) => s"which expands to ${ts.map(typeShortCode).mkString("(", ", ", ")")}"
                case ParamExpansion.Forged(bundled, _) => s"which stands for ${typeShortCode(bundled)}"
              badUse(s"Invalid use of kind-expanded type parameter ${typeShortCode(ref)} ($expansionMsg). It can only be used in type argument position.")
            case p: ParamRef =>
              p
            case t @ TypeRef(parent, name) =>
              checkNonOccurrence(marker, ctx, parent)
              t
        case t @ TermRef(prefix, ident) =>
          Ref.term(t) match
            case ctx.substitutesTermTo(u) =>
              u.symbol.termRef
            case _ =>
              prefix match
                case NoPrefix() => t
                case prefix => TermRef(decodeType(marker, localMarker, ctx, prefix), ident)
        case t: ThisType =>
          t
        case TypeBounds(lo, hi) =>
          TypeBounds(
            decodeType(marker, localMarker, ctx, lo),
            decodeType(marker, localMarker, ctx, hi),
          )
        case AndType(l, r) =>
          AndType(
            decodeType(marker, localMarker, ctx, l),
            decodeType(marker, localMarker, ctx, r),
          )
        case other =>
          unsupportedType(other)
    }

  private def decodeTerm(
    marker: TypeRef,
    kuotes: TermRef,
    localMarker: Option[TypeRef],
    rekindle: Option[TermRef], // Rekindle[marker, localMarker]
    ctx: DecodingContext,
    owner: Symbol,
    expr: Term,
  )(using
    Reporting.Context,
  ): Term =
    require(localMarker.isDefined == rekindle.isDefined)
    inside(expr) {
      expr match
        // '{ kuotes.splice[T](arg)[U] }
        case TypeApply(Apply(TypeApply(Select(prefix, "splice"), List(t)), List(arg)), List(u)) if prefix.tpe == kuotes =>
          // check that arg :《u》, ensuring that arg is usable in place where 《u》 is expected
          val decodedU =
            decodeType(marker, localMarker, ctx, u.tpe)
          val decodedUType =
            decodedU.asType.asInstanceOf[Type[Any]]
          if (arg.asExpr.isExprOf(using decodedUType))
            arg.changeOwner(owner).asExprOf(using decodedUType).asTerm
          else
            given Printer[Tree] = Printer.TreeShortCode
            given Printer[TypeRepr] = Printer.TypeReprShortCode
            badUse(s"Got ${arg.show} of type ${t.show}, expected type ${decodedU.show} (which is the decoding of ${u.show})")

        // '{ kuotes.rekindle[R](f: [⋅⋅⋅[_]] => Rekindle[⋅⋅, ⋅⋅⋅] ?=> R) }
        case Apply(TypeApply(Select(prefix, "rekindle"), List(r)), List(f)) if prefix.tpe == kuotes =>
          if (localMarker.isDefined)
            unsupported(s"Nested rekindle")
          else
            val targetType = decodeType(marker, localMarker = None, ctx, r.tpe)
            val ParsedRekindleArg(localMarker, rekindle, retTp, body) = parseRekindleArg(f)
            val expr = decodeTerm(marker, kuotes, Some(localMarker), Some(rekindle.ref), ctx, owner, body)
            Typed(expr, TypeTree.of(using targetType.asType))

        // '{ rekindle.pack[T](x)[Code, As] }
        case TypeApply(Apply(TypeApply(Select(prefix, "pack"), List(t)), List(x)), List(code, as)) if rekindle.contains(prefix.tpe) =>
          val code1 = decodeType(marker, localMarker, ctx, code.tpe)
          val as1 = decodeType(marker, localMarker, ctx, as.tpe) // this is the key step: expand any ⋅⋅⋅[A] in As into a bundle of forged types of the right kinds
          val actualType = decodeType(marker, localMarker, ctx, t.tpe)
          val expectedType = decodeParameterizedType(code1, as1)
          if (!(actualType <:< expectedType))
            badUse(s"To pack the box, argument of type ${typeShortCode(expectedType)} is required, but got ${typeShortCode(actualType)}.")
          val x1 = decodeTerm(marker, kuotes, localMarker, rekindle, ctx, owner, x)
          val targetType = TypeRepr.of[Box].appliedTo(List(code1, as1))
          provided(owner.asQuotes):
            targetType.asType match
              case '[tt] => '{ ${x1.asExpr}.asInstanceOf[tt] }.asTerm

        // '{ rekindle.unpack[Code, As](box)[T] }
        case TypeApply(Apply(TypeApply(Select(prefix, "unpack"), List(code, as)), List(box)), List(t)) if rekindle.contains(prefix.tpe) =>
          val code1 = decodeType(marker, localMarker, ctx, code.tpe)
          val as1 = decodeType(marker, localMarker, ctx, as.tpe) // this is the key step: expand any ⋅⋅⋅[A] in As into a bundle of forged types of the right kinds
          val expectedType = decodeType(marker, localMarker, ctx, t.tpe)
          val actualType = decodeParameterizedType(code1, as1)
          if (!(actualType <:< expectedType))
            badUse(s"The given box unpacks to ${typeShortCode(actualType)}, which is not a subtype of the expected ${typeShortCode(expectedType)}")
          val box1 = decodeTerm(marker, kuotes, localMarker, rekindle, ctx, owner, box)
          provided(owner.asQuotes):
            expectedType.asType match
              case '[t] => '{ ${box1.asExpr}.asInstanceOf[t] }.asTerm

        // '{ rekindle.substituteCo[H](x) }
        case Apply(TypeApply(Select(prefix, "substituteCo"), List(h)), List(x)) if rekindle.contains(prefix.tpe) =>
          val hg = h.tpe.appliedTo(localMarker.get)
          val targetType = decodeType(marker, localMarker, ctx, hg)
          val x1 = decodeTerm(marker, kuotes, localMarker, rekindle, ctx, owner, x)
          provided(owner.asQuotes):
            targetType.asType match
              case '[t] => '{ ${x1.asExpr}.asInstanceOf[t] }.asTerm

        // '{ rekindle.substituteContra[H](y) }
        case Apply(TypeApply(Select(prefix, "substituteContra"), List(h)), List(y)) if rekindle.contains(prefix.tpe) =>
          val hf = h.tpe.appliedTo(marker)
          val targetType = decodeType(marker, localMarker, ctx, hf)
          val y1 = decodeTerm(marker, kuotes, localMarker, rekindle, ctx, owner, y)
          provided(owner.asQuotes):
            targetType.asType match
              case '[t] => '{ ${y1.asExpr}.asInstanceOf[t] }.asTerm

        case k if k.tpe =:= kuotes =>
          badUse(s"Invalid use of ${treeShortCode(k)} in this position.")

        case r if rekindle.contains(r.tpe) =>
          badUse(s"Invalid use of ${treeShortCode(r)} in this position.")

        case PolyFun(tparams, params, paramsGiven, retTp, body) =>
          decodePolyFun(marker, kuotes, localMarker, rekindle, ctx, tparams, params, paramsGiven, retTp, body)
            .mkTerm(owner)
        case bl @ Block(List(stmt), Closure(method, optTp)) =>
          (stmt, method) match
            case (DefDef(name, paramss, retTp, Some(body)), Ident(methodName)) if methodName == name =>
              paramss match
                case (pc @ TermParamClause(params)) :: Nil => Symbol.noSymbol.termRef
                  decodeFun(
                    marker,
                    kuotes,
                    localMarker,
                    rekindle,
                    ctx,
                    paramsGiven = pc.isGiven,
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
          decodeBlock(marker, kuotes, localMarker, rekindle, ctx, owner, stmts, term)
        case Apply(f, as) =>
          val f1 = decodeTerm(marker, kuotes, localMarker, rekindle, ctx, owner, f)
          val bs = as.map(decodeTerm(marker, kuotes, localMarker, rekindle, ctx, owner, _))
          Apply(f1, bs)
        case TypeApply(f, ts) =>
          val f1 = decodeTerm(marker, kuotes, localMarker, rekindle, ctx, owner, f)
          val ts1 = expandTypeArgs(marker, localMarker, ctx, ts.map(_.tpe))
            .flatMap(_.toList)
          val ts2 = ts1.map(decodeType(marker, localMarker, ctx, _))
          TypeApply(f1, ts2.map(t => TypeTree.of(using t.asType)))
        case Select(prefix, name) =>
          val prefix1 = decodeTerm(marker, kuotes, localMarker, rekindle, ctx, owner, prefix)
          try {
            Select.unique(prefix1, name)
          } catch {
            e => unsupported(s"x.$name for overloaded method $name. In ${treeShortCode(prefix1)}.$name")
          }
        case Typed(x, t) =>
          Typed(
            decodeTerm(marker, kuotes, localMarker, rekindle, ctx, owner, x),
            TypeTree.of(using
              decodeType(marker, localMarker, ctx, t.tpe).asType
            ),
          )
        case New(tt) =>
          New(TypeTree.of(using decodeType(marker, localMarker, ctx, tt.tpe).asType))
        case i @ Ident(x) =>
          i match
            case ctx.substitutesTermTo(j) => j
            case i => i
        case l: Literal =>
          l
        case Repeated(as, tt) =>
          Repeated(
            as.map { a => decodeTerm(marker, kuotes, localMarker, rekindle, ctx, owner, a) },
            TypeTree.of(using decodeType(marker, localMarker, ctx, tt.tpe).asType),
          )
        case Inlined(call, bindings, expansion) =>
          val (ctx1, bindingFns) =
            bindings.mapS[DecodingContext, (fullCtx: DecodingContext) => Definition](ctx) {
              (ctx, binding) =>
                inside(binding) {
                  val (ctxElem, bindingFn) = decodeDefinition(marker, kuotes, localMarker, rekindle, ctx, owner, binding)
                  (ctx.push(ctxElem), bindingFn)
                }
            }
          val bindings1 = bindingFns.map(_(ctx1))
          Inlined(
            call,
            bindings1,
            insideInlinedCall(call):
              decodeTerm(marker, kuotes, localMarker, rekindle, ctx1, owner, expansion),
          )
        case other =>
          unimplemented(s"decodeTerm(${treeStruct(expr)})")
    }

  private def decodeBlock(
    marker: TypeRef,
    kuotes: TermRef,
    localMarker: Option[TypeRef],
    rekindle: Option[TermRef], // ev: Kuotes.Rekindle[marker, localMarker]
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
                val (ctxElem, stmtFn) = decodeDefinition(marker, kuotes, localMarker, rekindle, ctx, owner, defn)
                (ctx.push(ctxElem), stmtFn)
              case term: Term =>
                val term1 = decodeTerm(marker, kuotes, localMarker, rekindle, ctx, owner, term)
                (ctx, _ => term1)
              case other =>
                unimplemented(s"decoding statement ${treeShortCode(other)}\nTree: ${treeStruct(other)}")
          }
      }
    val stmts1 = stmtFns.map(_(ctx1))
    Block(stmts1, decodeTerm(marker, kuotes, localMarker, rekindle, ctx1, owner, expr))
  }

  private def decodeDefinition(
    marker: TypeRef,
    kuotes: TermRef,
    localMarker: Option[TypeRef],
    rekindle: Option[TermRef], // ev: Kuotes.Rekindle[marker, localMarker]
    ctx: DecodingContext,
    owner: Symbol,
    defn: Definition,
  )(using
    Reporting.Context,
  ): (DecodingContext.Elem, (fullCtx: DecodingContext) => Definition) = {
    defn match
      case v @ ValDef(name, tpt, Some(body)) =>
        val oldRef = v.symbol.termRef
        val newTpe = decodeType(marker, localMarker, ctx, tpt.tpe)
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
        , ctx => ValDef(newSym, Some(decodeTerm(marker, kuotes, localMarker, rekindle, ctx, owner = newSym, body)))
        )
      case t @ TypeDef(name, tree) =>
        tree match
          case TypeBoundsTree(lower, upper) =>
            if (lower.tpe =:= upper.tpe)
              val tpe = decodeType(marker, localMarker, ctx, lower.tpe)
              val sym = Symbol.newTypeAlias(
                owner,
                name,
                // t.symbol.flags, // throws an error
                Flags.EmptyFlags,
                tpe,
                privateWithin = Symbol.noSymbol,
              )
              ( DecodingContext.Elem.TypeSubstitution(t.symbol.typeRef, sym.typeRef)
              , ctx => TypeDef(sym)
              )
            else
              unsupported(s"TypeDef with different lower and upper bound: ${treeShortCode(t)} (${treeStruct(t)})")
          case other =>
            unimplemented(s"Type definition with rhs = ${treeShortCode(other)}\nTree: ${treeStruct(other)}")
      case other =>
        unimplemented(s"decoding definition ${treeShortCode(other)}\nTree: ${treeStruct(other)}")
  }

  private def decodePolyType(
    marker: TypeRepr,
    localMarker: Option[TypeRef],
    ctx: DecodingContext,
    pt: PolyType,
  )(using
    Reporting.Context,
  ): PolyType =
    val PolyType(tParamNames, tParamBounds, body) = pt

    val decodedTypeParams =
      decodeTypeParams(
        marker,
        localMarker,
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
        decodeType(marker, localMarker, ctx1, body)
      },
    )

  private def decodeMethodType(
    marker: TypeRepr,
    localMarker: Option[TypeRef],
    ctx: DecodingContext,
    methType: MethodType,
  )(using
    Reporting.Context,
  ): MethodType =
    val MethodType(paramNames, paramTypes, returnType) = methType
    MethodType(methType.methodTypeKind)(paramNames)(
      _ => paramTypes.map(t => decodeType(marker, localMarker, ctx, t)),
      _ => decodeType(marker, localMarker, ctx, returnType)
    )

  private case class DecodedPolyFun(
    tparamNames: Groups[String],
    tparamBounds: (tparams: Int => TypeRepr) => Groups[TypeBounds],
    paramsGiven: Boolean,
    paramNames: List[String],
    paramTypes: (tparams: Int => TypeRepr) => List[TypeRepr],
    returnType: (tparams: Int => TypeRepr) => TypeRepr,
    body: (newTParams: Int => TypeRepr, newParams: List[Term], owner: Symbol) => Term,
  ) {
    def mkTerm(owner: Symbol): Term =
      PolyFun(tparamNames.toFlatList, tparamBounds(_).toFlatList, paramsGiven, paramNames, paramTypes, returnType, body, owner)
  }

  private def decodePolyFun(
    marker: TypeRef,
    kuotes: TermRef,
    localMarker: Option[TypeRef],
    rekindle: Option[TermRef], // ev: Kuotes.Rekindle[marker, localMarker]
    ctx: DecodingContext,
    tparams: List[(name: String, kind: Either[TypeBounds, LambdaTypeTree], ref: TypeRef)],
    params: List[(name: String, tpe: TypeTree, ref: TermRef)],
    paramsGiven: Boolean,
    returnType: TypeTree,
    body: Term,
  )(using
    Reporting.Context,
  ): DecodedPolyFun = {
    val decodedTypeParams =
      decodeTypeParams(marker, localMarker, ctx, tparams)

    def tParamBounds1(tparams: Int => TypeRepr): List[TypeBounds] =
      decodedTypeParams.decodedBoundsFlat(tparams)

    val paramNames = params.map(_.name)

    def paramTypes(tparams: Int => TypeRepr): List[TypeRepr] =
      val ctx1 = decodedTypeParams.innerContext(tparams)
      params.map(t => decodeType(marker, localMarker, ctx1, t.tpe.tpe))

    def returnType1(tparams: Int => TypeRepr): TypeRepr =
      val ctx1 = decodedTypeParams.innerContext(tparams)
      decodeType(marker, localMarker, ctx1, returnType.tpe)

    def paramSubstitutions(newParams: List[Term]): List[DecodingContext.Elem.TermSubstitution] =
      (params zip newParams).map { case (pOld, pNew) =>
        DecodingContext.Elem.TermSubstitution(pOld.ref, pNew)
      }

    def body1(newTParams: Int => TypeRepr, newParams: List[Term], owner: Symbol): Term =
      val ctx1 = decodedTypeParams.innerContext(newTParams)
      val ctx2 = ctx1.pushAll(paramSubstitutions(newParams))
      decodeTerm(marker, kuotes, localMarker, rekindle, ctx2, owner, body)

    DecodedPolyFun(decodedTypeParams.decodedNames,  decodedTypeParams.decodedBounds, paramsGiven, paramNames, paramTypes, returnType1, body1)
  }

  private def decodeFun(
    marker: TypeRef,
    kuotes: TermRef,
    localMarker: Option[TypeRef],
    rekindle: Option[TermRef], // ev: Kuotes.Rekindle[marker, localMarker]
    ctx: DecodingContext,
    paramsGiven: Boolean,
    params: List[(name: String, tpe: TypeTree, ref: TermRef)],
    returnType: TypeTree,
    body: Term,
    owner: Symbol,
  )(using
    Reporting.Context,
  ): Term = {

    val paramNames = params.map(_.name)

    val paramTypes =
      params.map(t => decodeType(marker, localMarker, ctx, t.tpe.tpe))

    val returnType1: TypeRepr =
      decodeType(marker, localMarker, ctx, returnType.tpe)

    def paramSubstitutions(newParams: List[Term]): List[DecodingContext.Elem.TermSubstitution] =
      (params zip newParams).map { case (pOld, pNew) =>
        DecodingContext.Elem.TermSubstitution(pOld.ref, pNew)
      }

    def body1(newParams: List[Term], owner: Symbol): Term =
      val ctx1 = ctx.pushAll(paramSubstitutions(newParams))
      decodeTerm(marker, kuotes, localMarker, rekindle, ctx1, owner, body)

    val paramsKind = if paramsGiven then MethodTypeKind.Contextual else MethodTypeKind.Plain
    Lambda(
      owner = owner,
      tpe = MethodType(paramsKind)(paramNames)(_ => paramTypes, _ => returnType1),
      rhsFn = (sym, argTrees) => {
        val args = argTrees.map(_.asInstanceOf[Term])
        body1(args, sym)
      },
    )
  }

  private def decodeTypeParams(
    marker: TypeRepr,
    localMarker: Option[TypeRef],
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

    DecodedTypeParams(marker, localMarker, ctx, expandedTParams)
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
    localMarker: Option[TypeRef],
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
      val bounds1 = bounds0.map(decodeTypeBounds(marker, localMarker, ctx1, _))
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
      localMarker: Option[TypeRef],
      ctx: DecodingContext,
      expandedTypeParams: List[PostExpansionParam],
    ): DecodedTypeParams =
      val expandedTypeParamsWithIndex: List[(Int, PostExpansionParam)] =
        expandedTypeParams
          .mapS(0) { (j, p) => (j + p.expandedSize, (j, p)) }
          ._2
      new DecodedTypeParams(marker, localMarker, ctx, expandedTypeParamsWithIndex)
  }

  private def expandTypeArgs(
    marker: TypeRepr,
    localMarker: Option[TypeRef],
    ctx: DecodingContext,
    targs: List[TypeRepr],
  )(using
    Reporting.Context,
  ): List[SingleOrMultiple[TypeRepr]] = {
    import DecodingContext.ParamExpansion
    targs.map { ta =>
      inside(ta) {
        ta match {
          case fa @ AppliedType(f, targs) =>
            Single:
              if (f =:= marker)
                expandAndBundleTypeArg(marker, ctx, targs, forceExplicitBundle = false)
              else if (localMarker.exists(f =:= _))
                expandAndBundleTypeArg(localMarker.get, ctx, targs, forceExplicitBundle = true)
              else
                fa
          case ParamRefOrTypeRef(ref) =>
            ref match
              case ctx.expandsTo(x) =>
                x match
                  case ParamExpansion.StaticallyKnown(ps) =>
                    ps
                  case ParamExpansion.Forged(bundled, kinds) if localMarker.isDefined =>
                    // can expand to forged types only within rekindle, i.e. when localMarker is defined
                    kinds.map(kindToUpperBound)
                  case ParamExpansion.Forged(bundled, kinds) =>
                    badUse(s"Cannot statically determine the expanded form of type parameter ${typeShortCode(ref)}. It is only known to stand for ${typeShortCode(bundled)}. Hint: Wrap inside `rekindle` to expand such statically unknown types.")
              case _ =>
                Single(ref)
          case other =>
            Single(other)
        }
      }
    }
  }

  /**
   * @param forceExplicitBundle When `true`, ensure the expanded shape of ⋅⋅[A0], where A0 <: ⋅⋅[K],
   *   has the expected kind(s), even at the cost of forging correspondingly shaped types when
   *   the actual argument is too abstract to reveal such shape.
   */
  private def expandAndBundleTypeArg(
    marker: TypeRepr,
    ctx: DecodingContext,
    targs: List[TypeRepr],
    forceExplicitBundle: Boolean,
  )(using
    Reporting.Context,
  ): TypeRepr =
    // encode the expanded argument (A --> A1, ...) into a single type A1 :: ...
    val m = typeShortCode(marker)
    val a = targs.getSingle(otherwise = assertionFailed(s"Expected 1 type argument to $m, got ${targs.size} (${targs.map(typeShortCode).mkString(", ")})"))
    val a1: ParamRef | TypeRef = a match
      case a: ParamRef => a
      case a: TypeRef  => a
      case a           => badUse(s"Invalid application of $m. Spread operator $m can only be applied to type parameters, but ${typeShortCode(a)} is not one.")
    a1 match
      case ctx.expandsTo(as) =>
        as.bundled(forceExplicitBundle)
      case a1 =>
        badUse(s"Invalid application of $m. ${typeShortCode(a1)} is not <: $m[<kinds>]")

  private def decodeTypeBounds(
    marker: TypeRepr,
    localMarker: Option[TypeRef],
    ctx: DecodingContext,
    bounds: Either[TypeBounds, LambdaTypeTree],
  )(using
    Reporting.Context,
  ): TypeBounds =
    bounds match
      case Left(tb @ TypeBounds(lo, hi)) =>
        inside(tb):
          TypeBounds(
            decodeType(marker, localMarker, ctx, lo),
            decodeType(marker, localMarker, ctx, hi),
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
              localMarker,
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
                  case Left(t)    => decodeType(marker, localMarker, ctx1, t)
                  case Right(ltt) => decodeTypeBounds(marker, localMarker, ctx1, Right(ltt))
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
