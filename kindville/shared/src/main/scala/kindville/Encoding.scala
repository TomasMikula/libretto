package kindville

import kindville.Reporting.*
import kindville.util.{Groups, SingleOrMultiple, SourcePos}
import kindville.util.SingleOrMultiple.{Multiple, Single}
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
      case AppliedType(f, args) if f =:= TypeRepr.of[->] =>
        args match
          case inKs :: outK :: Nil =>
            FastReject.Success:
              val in = decodeKindOrKinds(inKs)
              val ks = in.left.map(Kinds.single).merge // TODO: Is it really OK to conflate a single-kind (e.g. `*`) with a singleton multi-kind (`* :: TNil`)?
              val l  = decodeKind(outK)
              Kind.arr(ks, l)
          case _ =>
            assertionFailed(s"Unexpected number of type arguments to ${Printer.TypeReprShortCode.show(f)}. Expected 2, got ${args.size}: ${args.map(Printer.TypeReprShortCode.show(_).mkString(", "))}")
      case other =>
        FastReject.Reject(expectedOneOf = List(typeShortCode(TypeRepr.of[*]), typeShortCode(TypeRepr.of[->])))

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

  /** Auxiliary markers (types and terms) used to guide decoding in coded expressions.
    *
    * The markers themselves are eraased during.
    *
    * In
    *
    * ```
    * [⋅⋅[_]] => (k: Kuotes[⋅⋅]) ?=>
    *   // ...
    *   val k1: k.type = k
    *   // ...
    *   kuotes.rekind:
    *     [⋅⋅⋅[_]] => (r: Kuotes.Rekind[⋅⋅, ⋅⋅⋅]) ?=>
    *       // ...
    * ```
    *
    * @param spreadAndBundle refers to `⋅⋅`
    * @param kuotes refers to `k`
    * @param kuotesAliases any aliases of `k`, such as `k1`
    * @param rekind `bundle` refers to `⋅⋅⋅`, `rekind` refers to `r`
    */
  case class TermMarkers(
    spreadAndBundle: TypeRef,
    kuotes: TermRef,
    kuotesAliases: List[TermRef],
    rekind: Option[(
      bundle: TypeRef,
      rekind: TermRef,
    )],
  ) {
    def isKuotes(k: Term): Boolean =
      k.tpe =:= kuotes || kuotesAliases.exists(k.tpe =:= _)

    def isRekind(r: Term): Boolean =
      rekind.exists(_.rekind == r.tpe)

    def withRekind(rekindedBundle: TypeRef, rekind: TermRef): TermMarkers =
      require(this.rekind.isEmpty, "cannot override rekind")
      copy(rekind = Some((rekindedBundle, rekind)))

    def withKuotesAlias(ref: TermRef): TermMarkers =
      copy(kuotesAliases = ref :: kuotesAliases)

    def typeMarkers: TypeMarkers =
      TypeMarkers(spreadAndBundle, rekind.map(_.bundle))
  }

  case class TypeMarkers(
    spreadAndBundle: TypeRepr,
    rekindedBundle: Option[TypeRef],
  ) {
    def isSpreadOperator(f: TypeRepr): Boolean =
      f =:= spreadAndBundle

    def isRekindedBundleOperator(f: TypeRepr): Boolean =
      rekindedBundle.exists(f =:= _)
  }

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
          val markers =
            TypeMarkers(marker, rekindedBundle = None)
          body match
            case inner @ TypeLambda(paramNames, paramBounds, body) =>
              val params =
                (paramNames zip paramBounds).zipWithIndex map { case ((n, b), i) =>
                  inner.param(i) match
                    case pi @ ParamRef(_, _) => (n, Left(b), pi)
                    case other => unexpectedTypeParamType(other)
                }
              val decodedTypeParams =
                decodeTypeParams(marker, params)
              TypeLambdaTemplate(
                decodedTypeParams.decodedNames,
                boundsFn = tparams => decodedTypeParams.decodedBounds,
                bodyFn   = tparams => {
                  val ctx = decodedTypeParams.extendContext(DecodingContext.empty, tparams)
                  decodeType(markers, ctx, body)
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
              decodeType(TypeMarkers(marker, rekindedBundle = None), substitutions, body)
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

      val markers =
        TermMarkers(marker, kuotesParam.ref, kuotesAliases = Nil, rekind = None)

      decodeTerm(markers, ctx = DecodingContext.empty, Symbol.spliceOwner, payload)
        .asExpr
    }

  def decodeExprT[As](
    encoded: Expr[[⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any],
    considering: Seq[Expr[? ofKinds ?]],
  )(using
    Type[As],
    Reporting.Context,
  ): Expr[Any] =
    inside(encoded.asTerm) {
      val ParseKuotedResult(marker, kuotesParam, _, payload) =
        parseKuoted(encoded)

      val markers =
        TermMarkers(marker, kuotesParam.ref, kuotesAliases = Nil, rekind = None)

      val (userTParams, params, paramsGiven, retTp, body) =
        doParsePolyFun(payload)

      if (params.nonEmpty)
        inside(payload) {
          badUse(s"Expected a no-value-arg function literal `[...] => () => <body>`, got a function with ${params.size} value parameter(s): ${params.map(_.name).mkString(", ")}")
        }

      val targs =
        unbundleTypeArgsOrFail(TypeRepr.of[As])

      val ctx =
        decodeTypeParamSubstitutions(marker, userTParams, targs, considering)

      decodeTerm(markers, ctx, Symbol.spliceOwner, body)
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

  private case class ParsedRekindArg(
    bundle: TypeRef,
    rekind: (name: String, tpe: TypeTree, ref: TermRef), // Kuotes.Rekind[⋅⋅, ⋅⋅⋅]
    retTp: TypeTree,
    body: Term,
  )

  private def parseRekindArg(
    f: Term,
  )(using
    Reporting.Context,
  ): ParsedRekindArg =
    inside(treeShortCode(f)) {
      f match
        case PolyFun(tparams, params, paramsGiven, retTp, body) =>
          val (_, _, rekindedBundle) =
            tparams.getSingle(otherwise = badUse(s"Expected a polymorphic function with 1 type parameter, but got ${tparams.size}"))
          val rekind =
            params.getSingle(otherwise = badUse(s"Expected a polymorphic function with 1 given value parameter, but got ${params.size} value paramters"))
          if (!paramsGiven)
            badUse(s"Expected a polymorphic function with a given value parameter, but ${rekind.name} is not given")
          ParsedRekindArg(rekindedBundle, rekind, retTp, body)
        case Inlined(call, Nil, expansion) =>
          insideInlinedCall(call):
            parseRekindArg(expansion)
        case other =>
          unsupported(s"Expected a polymorphic function `[⋅⋅⋅[_]] => (ev: Kuotes.Rekind[⋅⋅, ⋅⋅⋅]) ?=> ...`, got ${treeStruct(f)}")
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
      }
  }

  private def matchTypeAgainstKinds(
    kinds: TypeRepr,
    tArg: TypeRepr,
  )(using
    Reporting.Context,
  ): Either[
    (error: String, decodedKinds: SingleOrMultiple[Kind]),
    SingleOrMultiple[TypeRepr]
  ] = {
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

    alignedArgsToKinds
      .flatMap(_.traverse {
        case (k, t) =>
          val expectedUpperBound = kindToUpperBound(k)
          if (t <:< expectedUpperBound)
            Right(t)
          else
            Left(s"Type ${typeShortCode(t)} does not have the expected kind ${k.show} (because it is not a subtype of ${typeShortCode(expectedUpperBound)})")
      })
      .left.map((_, decodedKinds))
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

    inside(s"matching type argument ${typeShortCode(tArg)} against the kind(s) ${typeShortCode(kinds)} declared by the corresponding type parameter ${typeShortCode(formalTParam)}") {
      matchTypeAgainstKinds(kinds, tArg) match
        case Right(ts) =>
          TypeArgExpansion(formalTParam, ts)
        case Left((msg, decodedKinds)) =>
          val tOfKindsK = TypeRepr.of[ofKinds].appliedTo(List(tArg, kinds))
          Implicits.search(tOfKindsK) match
            case iss: ImplicitSearchSuccess =>
              TypeArgForgedExpansion(formalTParam, bundledArg = tArg, decodedKinds)
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
  }

  def compiletimeKindCheck[A <: AnyKind, K](using Type[A], Type[K], Reporting.Context): Expr[Unit] =
    matchTypeAgainstKinds(kinds = TypeRepr.of[K], tArg = TypeRepr.of[A]) match
      case Right(_) => '{ () }
      case Left((msg, _)) => badUse(msg)

  private def decodeType(
    markers: TypeMarkers,
    ctx: DecodingContext,
    body: TypeRepr,
  )(using
    Reporting.Context,
  ): TypeRepr =
    inside(body) {
      body match
        case r @ Refinement(base, memName, memType) =>
          Refinement(
            decodeType(markers, ctx, base),
            memName,
            decodeType(markers, ctx, memType),
          )
        case pt: PolyType =>
          decodePolyType(markers, ctx, pt)
        case mt: MethodType =>
          decodeMethodType(markers, ctx, mt)
        case AppliedType(f, targs) =>
          if (markers.isSpreadOperator(f))
            expandAndBundleTypeArg(f, ctx, targs, forceExplicitBundle = false)
          else if (markers.isRekindedBundleOperator(f))
            expandAndBundleTypeArg(f, ctx, targs, forceExplicitBundle = true)
          else
            val f1 = decodeType(markers, ctx, f)
            val targs1 = expandTypeArgs(markers, ctx, targs)
              .flatMap(_.toList)
            val targs2 = targs1.map(decodeType(markers, ctx, _))
            f1.appliedTo(targs2)
        case l @ TypeLambda(names, bounds, body) =>
          val decodedTypeParams =
            decodeTypeParams(
              markers.spreadAndBundle,
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
            tl => decodedTypeParams.decodedBoundsFlat,
            tl => {
              val ctx1 = decodedTypeParams.extendContext(ctx, tl.param)
              decodeType(markers, ctx1, body)
            },
          )
        case t if markers.isSpreadOperator(t) =>
          badUse(s"Cannot use the spread operator ${typeShortCode(t)} here")
        case t if markers.isRekindedBundleOperator(t) =>
          badUse(s"Cannot use the rekinded bundle operator ${typeShortCode(t)} here")
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
              checkNonOccurrence(markers.spreadAndBundle, ctx, parent)
              markers.rekindedBundle.foreach:
                checkNonOccurrence(_, ctx, parent)
              t
        case t @ TermRef(prefix, ident) =>
          Ref.term(t) match
            case ctx.substitutesTermTo(u) =>
              u.symbol.termRef
            case _ =>
              prefix match
                case NoPrefix() => t
                case prefix => TermRef(decodeType(markers, ctx, prefix), ident)
        case t: ThisType =>
          t
        case TypeBounds(lo, hi) =>
          TypeBounds(
            decodeType(markers, ctx, lo),
            decodeType(markers, ctx, hi),
          )
        case AndType(l, r) =>
          AndType(
            decodeType(markers, ctx, l),
            decodeType(markers, ctx, r),
          )
        case other =>
          unsupportedType(other)
    }

  private def decodeTerm(
    markers: TermMarkers,
    ctx: DecodingContext,
    owner: Symbol,
    expr: Term,
  )(using
    Reporting.Context,
  ): Term =
    inside(expr) {
      expr match
        // '{ kuotes.splice[T](arg)[U] }
        case TypeApply(Apply(TypeApply(Select(prefix, "splice"), List(t)), List(arg)), List(u)) if markers.isKuotes(prefix) =>
          // check that arg :《u》, ensuring that arg is usable in place where 《u》 is expected
          val decodedU =
            decodeType(markers.typeMarkers, ctx, u.tpe)
          val decodedUType =
            decodedU.asType.asInstanceOf[Type[Any]]
          if (arg.asExpr.isExprOf(using decodedUType))
            arg.changeOwner(owner).asExprOf(using decodedUType).asTerm
          else
            given Printer[Tree] = Printer.TreeShortCode
            given Printer[TypeRepr] = Printer.TypeReprShortCode
            badUse(s"Got ${arg.show} of type ${t.show}, expected type ${decodedU.show} (which is the decoding of ${u.show})")

        // '{ kuotes.rekind[R](f: [⋅⋅⋅[_]] => Rekind[⋅⋅, ⋅⋅⋅] ?=> R) }
        case Apply(TypeApply(Select(prefix, "rekind"), List(r)), List(f)) if markers.isKuotes(prefix) =>
          if (markers.rekind.isDefined)
            unsupported(s"Nested rekind")
          else
            val targetType = decodeType(markers.typeMarkers, ctx, r.tpe)
            val ParsedRekindArg(rekindedBundle, rekind, retTp, body) = parseRekindArg(f)
            val markers1 = markers.withRekind(rekindedBundle, rekind.ref)
            val expr = decodeTerm(markers1, ctx, owner, body)
            Typed(expr, TypeTree.of(using targetType.asType))

        // '{ rekind.pack[T](x)[Code, As] }
        case TypeApply(Apply(TypeApply(Select(prefix, "pack"), List(t)), List(x)), List(code, as)) if markers.isRekind(prefix) =>
          val code1 = decodeType(markers.typeMarkers, ctx, code.tpe)
          val as1 = decodeType(markers.typeMarkers, ctx, as.tpe) // this is the key step: expand any ⋅⋅⋅[A] in As into a bundle of forged types of the right kinds
          val actualType = decodeType(markers.typeMarkers, ctx, t.tpe)
          val expectedType = decodeParameterizedType(code1, as1)
          if (!(actualType <:< expectedType))
            badUse(s"To pack the box, argument of type ${typeShortCode(expectedType)} is required, but got ${typeShortCode(actualType)}.")
          val x1 = decodeTerm(markers, ctx, owner, x)
          val targetType = TypeRepr.of[Box].appliedTo(List(code1, as1))
          provided(owner.asQuotes):
            targetType.asType match
              case '[tt] => '{ ${x1.asExpr}.asInstanceOf[tt] }.asTerm

        // '{ rekind.unpack[Code, As](box)[T] }
        case TypeApply(Apply(TypeApply(Select(prefix, "unpack"), List(code, as)), List(box)), List(t)) if markers.isRekind(prefix) =>
          val as1 = decodeType(markers.typeMarkers, ctx, as.tpe) // this is the key step: expand any ⋅⋅⋅[A] in As into a bundle of *forged* types of the right kinds
          val expectedType = decodeType(markers.typeMarkers, ctx, t.tpe)
          val actualType = decodeParameterizedType(code.tpe, as1)
          if (!(actualType <:< expectedType))
            badUse(s"The given box unpacks to ${typeShortCode(actualType)}, which is not a subtype of the expected ${typeShortCode(expectedType)}")
          val box1 = decodeTerm(markers, ctx, owner, box)
          provided(owner.asQuotes):
            expectedType.asType match
              case '[t] => '{ ${box1.asExpr}.asInstanceOf[t] }.asTerm

        // '{ rekind.substituteCo[H](x) }
        case Apply(TypeApply(Select(prefix, "substituteCo"), List(h)), List(x)) if markers.isRekind(prefix) =>
          val hg = h.tpe.appliedTo(markers.rekind.get.bundle)
          val targetType = decodeType(markers.typeMarkers, ctx, hg)
          val x1 = decodeTerm(markers, ctx, owner, x)
          provided(owner.asQuotes):
            targetType.asType match
              case '[t] => '{ ${x1.asExpr}.asInstanceOf[t] }.asTerm

        // '{ rekind.substituteContra[H](y) }
        case Apply(TypeApply(Select(prefix, "substituteContra"), List(h)), List(y)) if markers.isRekind(prefix) =>
          val hf = h.tpe.appliedTo(markers.spreadAndBundle)
          val targetType = decodeType(markers.typeMarkers, ctx, hf)
          val y1 = decodeTerm(markers, ctx, owner, y)
          provided(owner.asQuotes):
            targetType.asType match
              case '[t] => '{ ${y1.asExpr}.asInstanceOf[t] }.asTerm

        case k if markers.isKuotes(k) =>
          badUse(s"Invalid use of ${treeShortCode(k)} in this position.")

        case r if markers.isRekind(r) =>
          badUse(s"Invalid use of ${treeShortCode(r)} in this position.")

        case PolyFun(tparams, params, paramsGiven, retTp, body) =>
          decodePolyFun(markers, ctx, tparams, params, paramsGiven, retTp, body)
            .mkTerm(owner)
        case bl @ Block(List(stmt), Closure(method, optTp)) =>
          (stmt, method) match
            case (DefDef(name, paramss, retTp, Some(body)), Ident(methodName)) if methodName == name =>
              paramss match
                case (pc @ TermParamClause(params)) :: Nil => Symbol.noSymbol.termRef
                  decodeFun(
                    markers,
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
          decodeBlock(markers, ctx, owner, stmts, term)
        case Apply(f, as) =>
          val f1 = decodeTerm(markers, ctx, owner, f)
          val bs = as.map(decodeTerm(markers, ctx, owner, _))
          Apply(f1, bs)
        case TypeApply(f, ts) =>
          val f1 = decodeTerm(markers, ctx, owner, f)
          val ts1 = expandTypeArgs(markers.typeMarkers, ctx, ts.map(_.tpe))
            .flatMap(_.toList)
          val ts2 = ts1.map(decodeType(markers.typeMarkers, ctx, _))
          TypeApply(f1, ts2.map(t => TypeTree.of(using t.asType)))
        case Select(prefix, name) =>
          val prefix1 = decodeTerm(markers, ctx, owner, prefix)
          try {
            Select.unique(prefix1, name)
          } catch {
            e => unsupported(s"x.$name for overloaded method $name. In ${treeShortCode(prefix1)}.$name")
          }
        case Typed(x, t) =>
          Typed(
            decodeTerm(markers, ctx, owner, x),
            TypeTree.of(using
              decodeType(markers.typeMarkers, ctx, t.tpe).asType
            ),
          )
        case New(tt) =>
          New(TypeTree.of(using decodeType(markers.typeMarkers, ctx, tt.tpe).asType))
        case i @ Ident(x) =>
          i match
            case ctx.substitutesTermTo(j) => j
            case i => i
        case l: Literal =>
          l
        case Repeated(as, tt) =>
          Repeated(
            as.map { a => decodeTerm(markers, ctx, owner, a) },
            TypeTree.of(using decodeType(markers.typeMarkers, ctx, tt.tpe).asType),
          )
        case Inlined(call, bindings, expansion) =>
          val ((markers1, ctx1), bindingFns) =
            bindings.mapS[(TermMarkers, DecodingContext), Option[(fullCtx: DecodingContext) => Definition]]((markers, ctx)) {
              case ((markers, ctx), binding) =>
                inside(binding) {
                  decodeDefinition(markers, ctx, owner, binding) match
                    case DecodeDefinitionResult.DecodedDefn(ctxElem, bindingFn) =>
                      ((markers, ctx.push(ctxElem)), Some(bindingFn))
                    case DecodeDefinitionResult.KuotesAlias(ref) =>
                      ((markers.withKuotesAlias(ref), ctx), None)
                }
            }
          val bindings1 = bindingFns.flatten.map(_(ctx1))
          Inlined(
            call,
            bindings1,
            insideInlinedCall(call):
              decodeTerm(markers1, ctx1, owner, expansion),
          )
        case other =>
          unimplemented(s"decodeTerm(${treeStruct(expr)})")
    }

  private def decodeBlock(
    markers: TermMarkers,
    ctx: DecodingContext,
    owner: Symbol,
    stmts: List[Statement],
    expr: Term,
  )(using
    Reporting.Context,
  ): Block = {
    val ((markers1, ctx1), stmtFns) =
      stmts.mapS[(TermMarkers, DecodingContext), Option[(fullCtx: DecodingContext) => Statement]]((markers, ctx)) {
        case ((markers, ctx), stmt) =>
          inside(stmt) {
            stmt match
              case defn: Definition =>
                decodeDefinition(markers, ctx, owner, defn) match
                  case DecodeDefinitionResult.DecodedDefn(ctxElem, defnFn) =>
                    ((markers, ctx.push(ctxElem)), Some(defnFn))
                  case DecodeDefinitionResult.KuotesAlias(ref) =>
                    ((markers.withKuotesAlias(ref), ctx), None)
              case term: Term =>
                val term1 = decodeTerm(markers, ctx, owner, term)
                ((markers, ctx), Some(_ => term1))
              case other =>
                unimplemented(s"decoding statement ${treeShortCode(other)}\nTree: ${treeStruct(other)}")
          }
      }
    val stmts1 = stmtFns.flatten.map(_(ctx1))
    Block(stmts1, decodeTerm(markers1, ctx1, owner, expr))
  }

  private enum DecodeDefinitionResult:
    case DecodedDefn(substitution: DecodingContext.Elem, decodedDefn: (fullCtx: DecodingContext) => Definition)
    case KuotesAlias(ref: TermRef)

  private def decodeDefinition(
    markers: TermMarkers,
    ctx: DecodingContext,
    owner: Symbol,
    defn: Definition,
  )(using
    Reporting.Context,
  ): DecodeDefinitionResult = {
    defn match
      // support direct aliases of the Kuotes instance. Needed because compiler tends to generate code like
      //
      //     val Kuotes_this: kuotes.type = kuotes
      //
      // when passing `kuotes` to an inline call.
      case v @ ValDef(name, tpt, Some(body)) if markers.isKuotes(body) =>
        DecodeDefinitionResult.KuotesAlias(v.symbol.termRef)

      case v @ ValDef(name, tpt, Some(body)) =>
        val oldRef = v.symbol.termRef
        val newTpe = decodeType(markers.typeMarkers, ctx, tpt.tpe)
        val flags = v.symbol.flags
        val newSym = Symbol.newVal(
          owner,
          name,
          newTpe,
          // v.symbol.flags,  // throws an error (https://github.com/scala/scala3/issues/25412)
          Flags.EmptyFlags,
          privateWithin = Symbol.noSymbol,
        )
        DecodeDefinitionResult.DecodedDefn(
          DecodingContext.Elem.TermSubstitution(oldRef,  Ref.term(newSym.termRef)),
          ctx => ValDef(newSym, Some(decodeTerm(markers, ctx, owner = newSym, body))),
        )

      case t @ TypeDef(name, tree) =>
        tree match
          case TypeBoundsTree(lower, upper) =>
            if (lower.tpe =:= upper.tpe)
              val tpe = decodeType(markers.typeMarkers, ctx, lower.tpe)
              val sym = Symbol.newTypeAlias(
                owner,
                name,
                // t.symbol.flags, // throws an error
                Flags.EmptyFlags,
                tpe,
                privateWithin = Symbol.noSymbol,
              )
              DecodeDefinitionResult.DecodedDefn(
                DecodingContext.Elem.TypeSubstitution(t.symbol.typeRef, sym.typeRef),
                ctx => TypeDef(sym),
              )
            else
              unsupported(s"TypeDef with different lower and upper bound: ${treeShortCode(t)} (${treeStruct(t)})")
          case other =>
            unimplemented(s"Type definition with rhs = ${treeShortCode(other)}\nTree: ${treeStruct(other)}")
      case other =>
        unimplemented(s"decoding definition ${treeShortCode(other)}\nTree: ${treeStruct(other)}")
  }

  private def decodePolyType(
    markers: TypeMarkers,
    ctx: DecodingContext,
    pt: PolyType,
  )(using
    Reporting.Context,
  ): PolyType =
    val PolyType(tParamNames, tParamBounds, body) = pt

    val decodedTypeParams =
      decodeTypeParams(
        markers.spreadAndBundle,
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
      pt => decodedTypeParams.decodedBoundsFlat,
      pt => {
        val ctx1 = decodedTypeParams.extendContext(ctx, pt.param)
        decodeType(markers, ctx1, body)
      },
    )

  private def decodeMethodType(
    markers: TypeMarkers,
    ctx: DecodingContext,
    methType: MethodType,
  )(using
    Reporting.Context,
  ): MethodType =
    val MethodType(paramNames, paramTypes, returnType) = methType
    MethodType(methType.methodTypeKind)(paramNames)(
      _ => paramTypes.map(t => decodeType(markers, ctx, t)),
      _ => decodeType(markers, ctx, returnType)
    )

  private case class DecodedPolyFun(
    tparamNames: Groups[String],
    tparamBounds: Groups[TypeBounds],
    paramsGiven: Boolean,
    paramNames: List[String],
    paramTypes: (tparams: Int => TypeRepr) => List[TypeRepr],
    returnType: (tparams: Int => TypeRepr) => TypeRepr,
    body: (newTParams: Int => TypeRepr, newParams: List[Term], owner: Symbol) => Term,
  ) {
    def mkTerm(owner: Symbol): Term =
      PolyFun(tparamNames.toFlatList, _ => tparamBounds.toFlatList, paramsGiven, paramNames, paramTypes, returnType, body, owner)
  }

  private def decodePolyFun(
    markers: TermMarkers,
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
      decodeTypeParams(markers.spreadAndBundle, tparams)

    val paramNames = params.map(_.name)

    def paramTypes(tparams: Int => TypeRepr): List[TypeRepr] =
      val ctx1 = decodedTypeParams.extendContext(ctx, tparams)
      params.map(t => decodeType(markers.typeMarkers, ctx1, t.tpe.tpe))

    def returnType1(tparams: Int => TypeRepr): TypeRepr =
      val ctx1 = decodedTypeParams.extendContext(ctx, tparams)
      decodeType(markers.typeMarkers, ctx1, returnType.tpe)

    def paramSubstitutions(newParams: List[Term]): List[DecodingContext.Elem.TermSubstitution] =
      (params zip newParams).map { case (pOld, pNew) =>
        DecodingContext.Elem.TermSubstitution(pOld.ref, pNew)
      }

    def body1(newTParams: Int => TypeRepr, newParams: List[Term], owner: Symbol): Term =
      val ctx1 = decodedTypeParams.extendContext(ctx, newTParams)
      val ctx2 = ctx1.pushAll(paramSubstitutions(newParams))
      decodeTerm(markers, ctx2, owner, body)

    DecodedPolyFun(decodedTypeParams.decodedNames, decodedTypeParams.decodedBounds, paramsGiven, paramNames, paramTypes, returnType1, body1)
  }

  private def decodeFun(
    markers: TermMarkers,
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
      params.map(t => decodeType(markers.typeMarkers, ctx, t.tpe.tpe))

    val returnType1: TypeRepr =
      decodeType(markers.typeMarkers, ctx, returnType.tpe)

    def paramSubstitutions(newParams: List[Term]): List[DecodingContext.Elem.TermSubstitution] =
      (params zip newParams).map { case (pOld, pNew) =>
        DecodingContext.Elem.TermSubstitution(pOld.ref, pNew)
      }

    def body1(newParams: List[Term], owner: Symbol): Term =
      val ctx1 = ctx.pushAll(paramSubstitutions(newParams))
      decodeTerm(markers, ctx1, owner, body)

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
    tParams: List[(name: String, kind: Either[TypeBounds, LambdaTypeTree], ref: ParamRef | TypeRef)],
  )(using
    Reporting.Context,
  ): DecodedTypeParams = {
    val decodedTParams: List[DecodedTypeParam] =
      tParams.map:
        case (name, bounds, origParam) =>
          DecodedTypeParam(name, origParam, boundsToKinds(marker, bounds))

    DecodedTypeParams(decodedTParams)
  }

  private case class DecodedTypeParam(originalName: String, originalParamRef: ParamRef | TypeRef, decodedKind: KindFromBounds) {

    def expandedSize: Int =
      decodedKind match
        case KindFromBounds.Single(_) => 1
        case KindFromBounds.AnyKind => 1
        case KindFromBounds.Spread(kinds) => kinds.size

    def names: SingleOrMultiple[String] =
      decodedKind match
        case KindFromBounds.Single(_) => Single(originalName)
        case KindFromBounds.AnyKind => Single(originalName)
        case KindFromBounds.Spread(kinds) =>
          kinds match
            case Single(k) => Single(originalName)
            case Multiple(ks) => Multiple(ks.zipWithIndex.map { case (_, i) => originalName + "$" + i })

    def bounds: SingleOrMultiple[TypeBounds] =
      decodedKind match
        case KindFromBounds.Spread(kinds) => kinds.map(kindToBounds)
        case KindFromBounds.Single(kind) => Single(kindToBounds(kind))
        case KindFromBounds.AnyKind => Single(TypeBounds.upper(TypeRepr.of[AnyKind]))

  }

  private class DecodedTypeParams(
    params: List[(index: Int, param: DecodedTypeParam)],
  ) {
    private lazy val names0: Groups[String] =
      Groups.fromList:
        params.map { case (_, p) => p.names }

    private lazy val bounds0: Groups[TypeBounds] =
      Groups.fromList:
        params.map { case (_, p) => p.bounds }

    def decodedNames: Groups[String] =
      names0

    def decodedNamesFlat: List[String] =
      decodedNames.toFlatList

    def extendContext(ctx: DecodingContext, actualTypeParams: Int => TypeRepr): DecodingContext =
      val newSubstitutions: List[DecodingContext.Elem] =
        params
          .map {
            case (j, DecodedTypeParam(_, origRef, kind)) =>
              kind match
                case KindFromBounds.Spread(ks) =>
                  DecodingContext.Elem.TypeArgExpansion(origRef, ks.zipWithIndex.map { case (_, i) => actualTypeParams(j + i) })
                case KindFromBounds.Single(_) | KindFromBounds.AnyKind =>
                  DecodingContext.Elem.TypeSubstitution(origRef, actualTypeParams(j))
          }
      ctx.pushAll(newSubstitutions)

    def decodedBounds: Groups[TypeBounds] =
      bounds0

    def decodedBoundsFlat: List[TypeBounds] =
      decodedBounds.toFlatList
  }

  private object DecodedTypeParams {
    def apply(
      params: List[DecodedTypeParam],
    ): DecodedTypeParams =
      val paramsWithIndex: List[(Int, DecodedTypeParam)] =
        params
          .mapS(0) { (j, p) => (j + p.expandedSize, (j, p)) }
          ._2
      new DecodedTypeParams(paramsWithIndex)
  }

  private def expandTypeArgs(
    markers: TypeMarkers,
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
              if (markers.isSpreadOperator(f))
                expandAndBundleTypeArg(f, ctx, targs, forceExplicitBundle = false)
              else if (markers.isRekindedBundleOperator(f))
                expandAndBundleTypeArg(f, ctx, targs, forceExplicitBundle = true)
              else
                fa
          case ParamRefOrTypeRef(ref) =>
            ref match
              case ctx.expandsTo(x) =>
                x match
                  case ParamExpansion.StaticallyKnown(ps) =>
                    ps
                  case ParamExpansion.Forged(bundled, kinds) if markers.rekindedBundle.isDefined =>
                    // can expand to forged types only within rekind, i.e. when rekindedBundle is defined
                    kinds.map(kindToUpperBound)
                  case ParamExpansion.Forged(bundled, kinds) =>
                    badUse(s"Cannot statically determine the expanded form of type parameter ${typeShortCode(ref)}. It is only known to stand for ${typeShortCode(bundled)}. Hint: Wrap inside `rekind` to expand such statically unknown types.")
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

  private enum KindFromBounds:
    case Spread(kinds: SingleOrMultiple[Kind]) // kind was declared using the spread operator ( <: ⋅⋅[K] )
    case Single(kind: Kind) // the kind is a single kind and was not declared using the spread operator at the top level
    case AnyKind

  private def boundsToKinds(
    marker: TypeRepr,
    bounds: Either[TypeBounds, LambdaTypeTree],
  )(using
    Reporting.Context,
  ): KindFromBounds =
    inside(s"Decoding kind(s) from bounds ${bounds.fold(typeShortCode, treeShortCode)}"):
      bounds match
        case Left(TypeBounds(lo, hi)) =>
          lo.asType match
            case '[Nothing] =>
              upperBoundToKinds(marker, hi)
            case other =>
              badUse:
                s"""Lower bounds not supported in coded expressions, but got lower bound (${typeShortCode(lo)}).
                  |Only upper bounds that indicate the kind are supported.
                  |Note: This means the usual bounds of type parameters are not supported at all in coded expressions."""
                  .stripMargin
        case Right(ltt @ LambdaTypeTree(typeDefs, body)) =>
          ltt.tpe match
            case TypeBounds(lo, tl: TypeLambda) if lo =:= TypeRepr.of[Nothing] =>
              KindFromBounds.Single(typeLambdaToKind(marker, tl))
            case other =>
              assertionFailed(s"Unexpected type of LambdaTypeTree. Expected TypeBounds(Nothing, TypeLambda(...)), got ${typeShortCode(other)}")

  private def upperBoundToKinds(
    marker: TypeRepr,
    upperBound: TypeRepr,
  )(using
    Reporting.Context,
  ): KindFromBounds =
    upperBound match
      case AppliedType(f, List(kinds)) if f =:= marker =>
        KindFromBounds.Spread:
          decodeKindOrKinds(kinds) match
            case Left(kind)   => Single(kind)
            case Right(kinds) => Multiple(kinds.toList)
      case t if t =:= TypeRepr.of[Any] =>
        KindFromBounds.Single(Kind.Tp)
      case tl: TypeLambda =>
        KindFromBounds.Single(typeLambdaToKind(marker, tl))
      case t if t =:= TypeRepr.of[AnyKind] =>
        KindFromBounds.AnyKind
      case other =>
        badUse(s"${typeShortCode(other)} is not as supported encoding of a kind or kinds.")

  /** Unlike [[upperBoundToKinds]], this method does not accept a potential multikind
    * (i.e. doesn't accept upper bound of `<: ⋅⋅[...]`, where ⋅⋅ is the spread operator),
    * nor does it accept the `<: AnyKind` bound.
    */
  private def upperBoundToKind(
    marker: TypeRepr,
    upperBound: TypeRepr,
  )(using
    Reporting.Context,
  ): Kind =
    upperBound match
      case t if t =:= TypeRepr.of[Any] =>
        Kind.Tp
      case tl: TypeLambda =>
        typeLambdaToKind(marker, tl)
      case AppliedType(f, List(kinds)) if f =:= marker =>
        badUse(s"The spread operator (${{typeShortCode(f)}}) not allowed in this position, because it has the potential to expand to multiple kinds, but only a single kind is allowed in this position.")
      case t if t =:= TypeRepr.of[AnyKind] =>
        badUse(s"AnyKind bound not allowed in this position.")
      case other =>
        badUse(s"${typeShortCode(other)} is not as supported encoding of a kind or kinds.")

  private def typeLambdaToKind(
    marker: TypeRepr,
    tl: TypeLambda,
  )(using
    Reporting.Context,
  ): Kind =
    inside(tl) {
      val TypeLambda(paramNames, paramBounds, body) = tl

      val paramKinds: Groups[Kind] =
        Groups.fromList:
          paramBounds.map: b =>
            boundsToKinds(marker, Left(b)) match
              case KindFromBounds.Spread(kinds) => kinds
              case KindFromBounds.Single(kind) => Single(kind)
              case KindFromBounds.AnyKind => badUse("AnyKind bound not supported in type lambda")


      val bodyKind: Kind =
        inside(body):
          upperBoundToKind(marker, body)

      Kind.arr(
        paramKinds.toFlatList, // flattening, i.e. losing information, but should be OK here
        bodyKind,
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
