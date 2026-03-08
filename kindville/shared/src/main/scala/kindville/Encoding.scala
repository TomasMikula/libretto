package kindville

import scala.quoted.*
import kindville.Reporting.*

private object Encoding {
  def apply(using q: Quotes)(): Encoding[q.type] =
    new Encoding[q.type]


  def encodeTypeArgs(using Quotes)(args: List[quotes.reflect.TypeRepr]): quotes.reflect.TypeRepr =
    import quotes.reflect.*
    args match
      case Nil => TypeRepr.of[TNil]
      case t :: ts => TypeRepr.of[::].appliedTo(List(t, encodeTypeArgs(ts)))

  def decodeTypeArgs[As <: AnyKind](args: Type[As])(using Quotes): List[Type[?]] =
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
                    h.asType :: decodeTypeArgs(t.asType)(using quotes)
                  case _ =>
                    report.errorAndAbort(s"Unexpected number of type arguments to ${Printer.TypeReprShortCode.show(f)}. Expected 2, got ${args.size}: ${args.map(Printer.TypeReprShortCode.show(_).mkString(", "))}")
              case other =>
                report.error(s"Cannot decode a list of type arguments from type ${Printer.TypeReprShortCode.show(repr)}")
                Nil
          case other =>
            report.error(s"Cannot decode a list of type arguments from type ${Printer.TypeReprShortCode.show(repr)}")
            Nil

  def decodeKind(using Quotes, Reporting.Context)(k: qr.TypeRepr): Kind =
    inside(k):
      decodeKind_(k) match
        case Right(k)  => k
        case Left(msg) => badUse(msg)

  private def decodeKind_(using Quotes)(k: qr.TypeRepr): Either[String, Kind] =
    import qr.*
    decodeKind__(k) match
      case Some(res) => res
      case None      => Left(s"Could not decode ${Printer.TypeReprShortCode.show(k)} as a kind.")

  private def decodeKind__(using Quotes)(k: qr.TypeRepr): Option[Either[String, Kind]] =
    import qr.*

    k match
      case tp if tp =:= TypeRepr.of[*] =>
        Some(Right(Kind.Tp))
      case AppliedType(f, args) if f =:= TypeRepr.of[->>] =>
        args match
          case inKs :: outK :: Nil =>
            Some(
              for
                in <- decodeKindOrKinds_(inKs)
                ks = in.left.map(Kinds.single).merge
                l  <- decodeKind_(outK)
              yield
                Kind.arr(ks, l)
            )
          case _ =>
            assertionFailed(s"Unexpected number of type arguments to ${Printer.TypeReprShortCode.show(f)}. Expected 2, got ${args.size}: ${args.map(Printer.TypeReprShortCode.show(_).mkString(", "))}")
      case other =>
        None

  def decodeKinds(using Quotes, Reporting.Context)(kinds: qr.TypeRepr): Kinds =
    inside(kinds):
      decodeKinds_(kinds) match
        case Right(ks) => ks
        case Left(msg) => badUse(msg)

  private def decodeKinds_(using Quotes)(kinds: qr.TypeRepr): Either[String, Kinds] =
    import qr.*
    decodeKinds__(kinds) match
      case Some(res) => res
      case None      => (new Exception).printStackTrace; Left(s"Cannot decode ${Printer.TypeReprShortCode.show(kinds)} as a list of kinds. Expected k1 :: k2 :: ... :: TNil")

  private def decodeKinds__(using Quotes)(kinds: qr.TypeRepr): Option[Either[String, Kinds]] =
    import qr.*

    kinds.dealiasKeepOpaques match
      case tnil if tnil =:= TypeRepr.of[TNil] =>
        Some(Right(Kinds.Empty))
      case AppliedType(f, args) if f =:= TypeRepr.of[::] =>
        args match
          case k :: ks :: Nil =>
            Some(
              for
                k  <- decodeKind_(k)
                ks <- decodeKinds_(ks)
              yield
                k :: ks
            )
          case _ =>
            assertionFailed(s"Unexpected number of type arguments to ${Printer.TypeReprShortCode.show(f)}. Expected 2, got ${args.size}: ${args.map(Printer.TypeReprShortCode.show(_).mkString(", "))}")
      case other =>
        None

  def decodeKindOrKinds(using Quotes, Reporting.Context)(ks: qr.TypeRepr): Either[Kind, Kinds] =
    inside(ks):
      decodeKindOrKinds_(ks) match
        case Right(r) => r
        case Left(e)  => badUse(e)

  def decodeKindOrKinds_(using Quotes)(ks: qr.TypeRepr): Either[String, Either[Kind, Kinds]] =
    import qr.*

    decodeKind__(ks) match
      case Some(Right(k)) => Right(Left(k))
      case Some(Left(e))  => Left(e)
      case None =>
        decodeKinds__(ks) match
          case Some(Right(ks)) => Right(Right(ks))
          case Some(Left(e))   => Left(e)
          case None =>
            Left(s"Could not decode ${Printer.TypeReprShortCode.show(ks)} as a kind(s).")

  def kindToBounds(k: Kind)(using Quotes): qr.TypeBounds =
    import qr.*

    TypeBounds(
      TypeRepr.of[Nothing],
      kindToUpperBound(k),
    )

  def kindsToBounds(ks: Kinds)(using Quotes): List[qr.TypeBounds] =
    import qr.*

    ks match
      case Kinds.Empty      => Nil
      case Kinds.Cons(h, t) => kindToBounds(h) :: kindsToBounds(t)

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

  enum ContextElem:
    case TypeSubstitution(src: ParamRef | TypeRef, tgt: TypeRepr)
    case TypeArgExpansion(src: ParamRef | TypeRef, tgt: List[TypeRepr])
    case TermSubstitution(src: TermRef, tgt: Term)

  extension (ctx: List[ContextElem])
    def substitutesTypeTo: TypeSubstitutionExtractor = TypeSubstitutionExtractor(ctx)
    def substitutesTermTo: TermSubstitutionExtractor = TermSubstitutionExtractor(ctx)
    def expandsTo: ExpansionExtractor = ExpansionExtractor(ctx)

  class TypeSubstitutionExtractor(ctx: List[ContextElem]):
    def unapply(p: ParamRef | TypeRef): Option[TypeRepr] =
      ctx.collectFirst { case ContextElem.TypeSubstitution(src, res) if src =:= p =>
        res
      }

  class TermSubstitutionExtractor(ctx: List[ContextElem]):
    def unapply(i: Ident): Option[Term] =
      ctx.collectFirst { case ContextElem.TermSubstitution(src, res) if src.termSymbol == i.symbol => res }

  class ExpansionExtractor(ctx: List[ContextElem]):
    def unapply(p: ParamRef | TypeRef): Option[List[TypeRepr]] =
      ctx.collectFirst { case ContextElem.TypeArgExpansion(src, res) if src =:= p => res }

  case class TypeLambdaTemplate(
    paramNames: List[String],
    boundsFn: (tparams: Int => TypeRepr) => List[TypeBounds],
    bodyFn:   (tparams: Int => TypeRepr) => TypeRepr,
  )

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
              val (names, cont) =
                decodeTypeParams(
                  marker,
                  ctx = Nil,
                  params
                )
              TypeLambdaTemplate(
                names,
                boundsFn = tparams => cont(tparams)._1,
                bodyFn   = tparams => {
                  val ctx = cont(tparams)._2
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
    inside("TODO: refine (xJdr)") {
      val args = decodeTypeArgs(Type.of[As])

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

  def decodeParameterizedTerm0(
    nameHint: Option[String],
    encoded: Expr[[⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any],
    args: List[Expr[Any]],
  )(using
    Reporting.Context,
  ): Expr[Any] =
    val ParseKuotedResult(marker, kuotesParam, _, payload) =
      parseKuoted(encoded)

    val (params, retTp, body) =
      doParseFun(payload)

    val f =
      decodeFun(marker, Some(kuotesParam.ref), ctx = Nil, params, retTp, body, Symbol.spliceOwner, nameHint)

    Select
      .unique(f, "apply")
      .appliedToArgs(args.map(_.asTerm))
      .asExpr

  def decodeParameterizedTerm1[As[⋅⋅[_]]](
    nameHint: Option[String],
    encoded: Expr[[⋅⋅[_]] => Kuotes[⋅⋅] ?=> Any],
    args: List[Expr[Any]],
  )(using
    Type[As],
    Reporting.Context,
  ): Expr[Any] =
    val ParseKuotedResult(marker, kuotesParam, _, payload) =
      parseKuoted(encoded)

    val (userTParams, params, retTp, body) =
      doParsePolyFun(payload)

    val targs =
      decodeTypeArgs(TypeRepr.of[As].appliedTo(marker).asType)
        .map(t => TypeRepr.of(using t).dealiasKeepOpaques)

    val ctx =
      decodeTypeParamSubstitutions(marker, userTParams, targs)

    val f =
      decodeFun(marker, Some(kuotesParam.ref), ctx, params, retTp, body, Symbol.spliceOwner, nameHint)

    Select
      .unique(f, "apply")
      .appliedToArgs(args.map(_.asTerm))
      .asExpr

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
        case i @ Inlined(call, Nil, expansion) =>
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
        case Inlined(_, Nil, expansion) =>
          doParsePolyFun(expansion)
        case other =>
          badUse(s"Expected a polymorphic function, got ${expr.show(using Printer.TreeStructure)}")
    }

  private def doParseFun(
    expr: Term,
  )(using
    Reporting.Context,
  ): (
    params: List[(name: String, tpe: qr.TypeTree, ref: qr.TermRef)],
    retTp: qr.TypeTree,
    body: qr.Term,
  ) =
    inside(expr) {
      expr match
        case Fun(params, retTp, body) =>
          (params, retTp, body)
        case Inlined(_, Nil, expansion) =>
          doParseFun(expansion)
        case other =>
          badUse(s"Expected a function literal (lambda), got ${expr.show(using Printer.TreeStructure)}")
    }

  object Fun {

    /** Matches a lambda `(a: A, ...) => body` */
    def unapply(expr: Term): Option[(
      params: List[(name: String, tpe: TypeTree, ref: TermRef)],
      retTp: TypeTree,
      body: Term,
    )] = {
      expr match
        case Block(List(stmt), Closure(method, optTp)) =>
          (stmt, method) match
            case (DefDef(name, paramss, retTp, Some(body)), Ident(methodName)) if methodName == name =>
              paramss match
                case TermParamClause(params) :: Nil =>
                  Some((
                    params.map { case v @ ValDef(name, tpe, _) => (name, tpe, v.symbol.termRef) },
                    retTp,
                    body,
                  ))
                case _ =>
                  None
            case _ =>
              None
        case _ =>
          None
    }
  }

  private def decodeTypeParamSubstitutions(
    marker: TypeRepr,
    tparams: List[(name: String, kind: Either[TypeBounds, LambdaTypeTree], ref: ParamRef | TypeRef)],
    targs: List[TypeRepr],
  )(using
    Reporting.Context,
  ): List[ContextElem] = {
    import ContextElem.{TypeSubstitution, TypeArgExpansion}

    if (tparams.size != targs.size)
      badUse(s"Expected ${targs.size} custom type parameters matching the arguments ${targs.map(t => typeShortCode(t)).mkString(", ")}. Got ${tparams.map(p => typeShortCode(p.ref)).mkString(", ")}")

    (tparams zip targs) map {
      case ((name, bounds, ref), t) =>
        inside("TODO: refine (pLdk)"):
          val elem: TypeSubstitution | TypeArgExpansion =
            bounds match
              case Left(TypeBounds(lower, upper)) =>
                upper match
                  case AppliedType(f, List(kinds)) if f =:= marker =>
                    lower.asType match
                      case '[Nothing] =>
                        decodeKindOrKinds(kinds) match
                          case Left(k) =>
                            // TODO: check `t` against `k`
                            TypeSubstitution(ref, t)
                          case Right(ks) =>
                            val ts = decodeTypeArgs(t.asType)
                            // TODO: check `ts` against `kinds`
                            TypeArgExpansion(ref, ts.map(TypeRepr.of(using _)))
                      case other =>
                        badUse(s"Cannot mix the \"spread\" upper bound (${typeShortCode(marker)}) with a lower bound (${typeShortCode(lower)})")
                  case _ =>
                    TypeSubstitution(ref, t)
              case Right(ltt) =>
                TypeSubstitution(ref, t)

          // decode since the provided type args may contain the marker
          elem match
            case TypeSubstitution(ref, t) =>
              TypeSubstitution(ref, decodeType(marker, ctx = Nil, t))
            case TypeArgExpansion(ref, ts) =>
              val ts1 = ts.map(decodeType(marker, ctx = Nil, _))
              TypeArgExpansion(ref, ts1)
    }
  }

  private def decodeType(
    marker: TypeRepr,
    ctx: List[ContextElem],
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
          val targs2 = targs1.map(decodeType(marker, ctx, _))
          f1.appliedTo(targs2)
        case l @ TypeLambda(names, bounds, body) =>
          val (names1, cont) =
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
          TypeLambda.apply(
            names1,
            tl => cont(tl.param)._1,
            tl => {
              val ctx1 = cont(tl.param)._2 ::: ctx
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
            case ctx.expandsTo(ps)        => badUse(s"Invalid use of kind-expanded type argument ${typeShortCode(p)}. It can only be used in type argument position.")
            case p                        => p
        case t @ TypeRef(parent, name) =>
          t match
            case ctx.substitutesTypeTo(u) => u
            case ctx.expandsTo(ts)        => badUse(s"Invalid use of kind-expanded type argument ${typeShortCode(t)}. It can only be used in type argument position.")
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
    kuotesOpt: Option[TermRef], // TODO: change to non-optional once we always use Kuotes
    ctx: List[ContextElem],
    owner: Symbol,
    expr: Term,
  )(using
    Reporting.Context,
  ): Term =
    inside(expr) {
      expr match
        // '{ kuotes.disguise[T](arg)[U] }
        case TypeApply(Apply(TypeApply(Select(prefix, "disguise"), List(t)), List(arg)), List(u)) if Some(prefix.tpe) == kuotesOpt =>
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
          decodePolyFun(marker, kuotesOpt, ctx, tparams, params, retTp, body, owner)
        case bl @ Block(List(stmt), Closure(method, optTp)) =>
          (stmt, method) match
            case (DefDef(name, paramss, retTp, Some(body)), Ident(methodName)) if methodName == name =>
              paramss match
                case TermParamClause(params) :: Nil => Symbol.noSymbol.termRef
                  decodeFun(
                    marker,
                    kuotesOpt,
                    ctx,
                    params.map { case v @ ValDef(name, tpe, _) => (name, tpe, v.symbol.termRef) },
                    retTp,
                    body,
                    owner,
                    nameHint = None,
                  )
                case _ =>
                  unsupported(s"Closure variant ${treeShortCode(bl)} (${treeStruct(bl)})")
            case _ =>
              unsupported(s"Closure variant ${treeShortCode(bl)} (${treeStruct(bl)})")
        case Block(stmts, term) =>
          decodeBlock(marker, kuotesOpt, ctx, owner, stmts, term)
        case Apply(f, as) =>
          val f1 = decodeTerm(marker, kuotesOpt, ctx, owner, f)
          val bs = as.map(decodeTerm(marker, kuotesOpt, ctx, owner, _))
          Apply(f1, bs)
        case TypeApply(f, ts) =>
          val f1 = decodeTerm(marker, kuotesOpt, ctx, owner, f)
          val ts1 = expandTypeArgs(marker, ctx, ts.map(_.tpe))
          val ts2 = ts1.map(decodeType(marker, ctx, _))
          TypeApply(f1, ts2.map(t => TypeTree.of(using t.asType)))
        case Select(prefix, name) =>
          val prefix1 = decodeTerm(marker, kuotesOpt, ctx, owner, prefix)
          try {
            Select.unique(prefix1, name)
          } catch {
            e => unsupported(s"x.m for overloaded m. In ${treeShortCode(prefix1)}.$name")
          }
        case Typed(x, t) =>
          Typed(
            decodeTerm(marker, kuotesOpt, ctx, owner, x),
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
            as.map { a => decodeTerm(marker, kuotesOpt, ctx, owner, a) },
            TypeTree.of(using decodeType(marker, ctx, tt.tpe).asType),
          )
        case i @ Inlined(call, bindings, expansion) =>
          Inlined(
            call,
            bindings,
            decodeTerm(marker, kuotesOpt, ctx, owner, expansion),
          ).changeOwner(owner)
        case other =>
          unimplemented(s"decodeTerm(${treeStruct(expr)})")
    }

  private def decodeBlock(
    marker: TypeRef | ParamRef,
    kuotesOpt: Option[TermRef], // TODO: change to non-optional once we always use Kuotes
    ctx: List[ContextElem],
    owner: Symbol,
    stmts: List[Statement],
    expr: Term,
  )(using
    Reporting.Context,
  ): Block = {
    val preprocessedStmts: List[(ContextElem, (fullCtx: List[ContextElem]) => Statement)] =
      stmts.map { stmt =>
        inside(stmt) {
          stmt match
            case v @ ValDef(name, tpt, Some(body)) =>
              val oldRef = v.symbol.termRef
              val newTpe = decodeType(marker, ctx, tpt.tpe) // TODO: ctx to include any definitions earlier in the block
              val flags = v.symbol.flags

              val newSym = Symbol.newVal(
                owner,
                name,
                newTpe,
                // v.symbol.flags,  // throws an error (https://github.com/scala/scala3/issues/25412)
                Flags.EmptyFlags,
                privateWithin = Symbol.noSymbol,
              )
              ( ContextElem.TermSubstitution(oldRef,  Ref.term(newSym.termRef))
              , ctx => ValDef(newSym, Some(decodeTerm(marker, kuotesOpt, ctx, owner = newSym, body)))
              )
            case other =>
              unimplemented(s"decoding statement ${treeShortCode(other)}\nTree: ${treeStruct(other)}")
        }
      }

    val ctx1 = preprocessedStmts.map(_._1) ::: ctx
    val stmts1 = preprocessedStmts.map(_._2(ctx1))
    Block(stmts1, decodeTerm(marker, kuotesOpt, ctx1, owner, expr))
  }

  private def decodePolyType(
    marker: TypeRepr,
    ctx: List[ContextElem],
    pt: PolyType,
  )(using
    Reporting.Context,
  ): PolyType =
    val PolyType(tParamNames, tParamBounds, body) = pt

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

    PolyType(tParamNames1)(
      pt => cont(pt.param)._1,
      pt => {
        val ctx1 = cont(pt.param)._2
        decodeType(marker, ctx1, body)
      },
    )

  private def decodeMethodType(
    marker: TypeRepr,
    ctx: List[ContextElem],
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
    kuotesOpt: Option[TermRef],
    ctx: List[ContextElem],
    tparams: List[(name: String, kind: Either[TypeBounds, LambdaTypeTree], ref: TypeRef)],
    params: List[(name: String, tpe: TypeTree, ref: TermRef)],
    returnType: TypeTree,
    body: Term,
    owner: Symbol,
  )(using
    Reporting.Context,
  ): Term = {
    val (tParamNames1, cont) =
      decodeTypeParams(marker, ctx, tparams)

    def tParamBounds1(tparams: Int => TypeRepr): List[TypeBounds] =
      cont(tparams)._1

    val paramNames = params.map(_.name)

    def paramTypes(tparams: Int => TypeRepr): List[TypeRepr] =
      val ctx1 = cont(tparams)._2
      params.map(t => decodeType(marker, ctx1, t.tpe.tpe))

    def returnType1(tparams: Int => TypeRepr): TypeRepr =
      val ctx1 = cont(tparams)._2
      decodeType(marker, ctx1, returnType.tpe)

    def paramSubstitutions(newParams: List[Term]): List[ContextElem.TermSubstitution] =
      (params zip newParams).map { case (pOld, pNew) =>
        ContextElem.TermSubstitution(pOld.ref, pNew)
      }

    def body1(newTParams: Int => TypeRepr, newParams: List[Term], owner: Symbol): Term =
      val ctx1 = cont(newTParams)._2
      val ctx2 = paramSubstitutions(newParams) ::: ctx1
      decodeTerm(marker, kuotesOpt, ctx2, owner, body)

    PolyFun(tParamNames1, tParamBounds1, paramNames, paramTypes, returnType1, body1, owner)
  }

  private def decodeFun(
    marker: TypeRef | ParamRef,
    kuotesOpt: Option[TermRef],
    ctx: List[ContextElem],
    params: List[(name: String, tpe: TypeTree, ref: TermRef)],
    returnType: TypeTree,
    body: Term,
    owner: Symbol,
    nameHint: Option[String],
  )(using
    Reporting.Context,
  ): Term = {

    val paramNames = params.map(_.name)

    val paramTypes =
      params.map(t => decodeType(marker, ctx, t.tpe.tpe))

    val returnType1: TypeRepr =
      decodeType(marker, ctx, returnType.tpe)

    def paramSubstitutions(newParams: List[Term]): List[ContextElem.TermSubstitution] =
      (params zip newParams).map { case (pOld, pNew) =>
        ContextElem.TermSubstitution(pOld.ref, pNew)
      }

    def body1(newParams: List[Term], owner: Symbol): Term =
      val ctx1 = paramSubstitutions(newParams) ::: ctx
      decodeTerm(marker, kuotesOpt, ctx1, owner, body)

    val nameSuffix =
      nameHint.getOrElse(owner.fullName)

    val methSym =
      Symbol.newMethod(
        owner,
        name = "$anonfun$" + nameSuffix,
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
    tParams: List[(name: String, kind: Either[TypeBounds, LambdaTypeTree], ref: ParamRef | TypeRef)],
  )(using
    Reporting.Context,
  ): (
    List[String],              // names of new type params
    TParamsFun[(List[TypeBounds], List[ContextElem])]
  ) = {
    enum PostExpansionParam:
      case Original(name: String, kind: Either[TypeBounds, LambdaTypeTree])
      case Expanded(params: Either[(String, Kind), List[(String, Kind)]])

    def expandParam(name: String, kinds: TypeRepr)(using Reporting.Context): Either[(String, Kind), List[(String, Kind)]] =
      decodeKindOrKinds(kinds) match
        case Left(kind)   => Left((name, kind))
        case Right(kinds) => Right(
          kinds
            .toList
            .zipWithIndex
            .map { case (bounds, i) => (name + "$" + i, bounds) }
        )

    def expandParams(
      i: Int,
      ps: List[(name: String, kind: Either[TypeBounds, LambdaTypeTree], ref: ParamRef | TypeRef)],
    )(using
      Reporting.Context,
    ): List[(PostExpansionParam, TParamsFun[ContextElem])] =
      inside("TODO: refine (PcXu)") {
        ps match
          case Nil =>
            Nil
          case (name, Left(bounds @ TypeBounds(lower, AppliedType(f, List(kinds)))), origParam) :: ps if f =:= marker =>
            lower.asType match
              case '[Nothing] =>
                val expanded = expandParam(name, kinds)
                val n = expanded.fold(_ => 1, _.size)
                val replacement: TParamsFun[ContextElem] =
                  tparams => ContextElem.TypeArgExpansion(origParam, List.range(0, n).map(j => tparams(i + j)))
                (PostExpansionParam.Expanded(expanded), replacement) :: expandParams(i + n, ps)
              case other =>
                badUse(s"Cannot mix the \"spread\" upper bound (${typeShortCode(marker)}) with a lower bound (${typeShortCode(lower)})")
          case (name, kind, origParam) :: ps =>
            ( PostExpansionParam.Original(name, kind)
            , tps => ContextElem.TypeSubstitution(origParam, tps(i))
            ) :: expandParams(i + 1, ps)
      }

    val (expandedTParams, replacements): (List[PostExpansionParam], List[TParamsFun[ContextElem]]) =
      expandParams(0, tParams).unzip

    val newSubstitutions: TParamsFun[List[ContextElem]] =
      tparams => replacements.map(_(tparams))

    val (names, bounds) =
      expandedTParams.flatMap:
        case PostExpansionParam.Original(name, bounds) => (name, bounds) :: Nil
        case PostExpansionParam.Expanded(Left((n, k))) => (n, Left(kindToBounds(k))) :: Nil
        case PostExpansionParam.Expanded(Right(ps))    => ps.map { case (n, k) => (n, Left(kindToBounds(k))) }
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
  )(using
    Reporting.Context,
  ): List[TypeRepr] =
    targs.flatMap { ta =>
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
                      encodeTypeArgs(as) :: Nil
                    case a1 =>
                      badUse(s"Invalid application of $m in ${typeShortCode(fa)}. ${typeShortCode(a1)} is not <: $m[<kinds>]")
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
      }
    }

  private def decodeTypeBounds(
    marker: TypeRepr,
    ctx: List[ContextElem],
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
          val (paramNames, cont) =
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
              paramNames,
              tl => cont(tl.param)._1,
              tl => {
                val ctx1 = cont(tl.param)._2
                bodyTpe match
                  case Left(t)    => decodeType(marker, ctx1, t)
                  case Right(ltt) => decodeTypeBounds(marker, ctx1, Right(ltt))
              }
            ),
          )
        }

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
