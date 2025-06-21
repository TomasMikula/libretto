package libretto.typology.toylang.types

import libretto.lambda.{MappedMorphism, MonoidalCategory, MonoidalObjectMap, Shuffle, Tupled, UnhandledCase}
import libretto.lambda.Tupled.*
import libretto.lambda.util.{Exists, SourcePos, TypeEq}
import libretto.lambda.util.Exists.Indeed
import libretto.lambda.util.TypeEq.Refl
import libretto.typology.kinds.*
import libretto.typology.types.{MultiTypeFun, OpenTypeExpr, PartialArgs, Routing, TypeExpr, TypeFun, kindShuffle}
import libretto.typology.types.kindShuffle.TransferOpt
import libretto.typology.util.Either3

opaque type Type[V] = TypeExpr[TypeConstructor[V, _, _], ○, ●]

object Type {
  private type OpenExpr[V, K, L] = OpenTypeExpr[TypeConstructor[V, _, _], K, L]

  def unit[V]: Type[V]   = TypeExpr.lift(TypeConstructor.UnitType())
  def int[V]: Type[V]    = TypeExpr.lift(TypeConstructor.IntType())
  def string[V]: Type[V] = TypeExpr.lift(TypeConstructor.StringType())

  def pair[V](a: Type[V], b: Type[V]): Type[V] =
    TypeExpr.App(
      TypeConstructor.Pair(),
      PartialArgs.introBoth(
        PartialArgs(a),
        PartialArgs(b),
      ),
    )

  def sum[V](a: Type[V], b: Type[V]): Type[V] =
    TypeExpr.App(
      TypeConstructor.Sum(),
      PartialArgs.introBoth(
        PartialArgs(a),
        PartialArgs(b),
      ),
    )

  def fix[V, K](f: TypeConstructor.Fix[V, K]): Type[V] =
    TypeExpr.lift(f)

  def fix[V](f: Fun[V, ●, ●]): Type[V] =
    fixDecompose(f) match
      case FixDecomposed.NothingToFix(t) =>
        t
      case FixDecomposed.CapturedArgs(args, pf) =>
        TypeFun.toExpr(args > Fun.pfix(pf))

  def fixDecompose[V](
    f: Fun[V, ●, ●],
  ): FixDecomposed[V] =
    OpenTypeExpr.open(f.expr) match
      case Left(t) =>
        UnhandledCase.raise(s"nothing to fix")
      case Right(Indeed((cpt, opn))) =>
        fixDecompose(cpt, opn) match
          case Either3.Left(ev) =>
            FixDecomposed.NothingToFix(f.expr.from(using ev.flip))
          case Either3.Middle(nothing) =>
            nothing
          case Either3.Right(Indeed((capt, expr))) =>
            import expr.inKind2
            val m = Routing.toMultiplier(f.pre)
            FixDecomposed.CapturedArgs(Args(capt), TypeConstructor.PFix(m, expr))

  def pfixDecompose[V](
    f: Fun[V, ● × ●, ●],
  ): PFixDecomposed[V] =
    OpenTypeExpr.open(f.expr) match
      case Left(t) =>
        UnhandledCase.raise(s"nothing to fix")
      case Right(Indeed((cpt, opn))) =>
        fixDecompose(cpt, opn) match
          case Either3.Left(ev) =>
            PFixDecomposed.NothingToFix(TypeFun(Routing.elim[●], f.expr.from(using ev.flip)))
          case Either3.Middle(x) =>
            x
          case Either3.Right(Indeed((capt, expr))) =>
            pfixDecompose(capt, f.pre, expr)

  private def pfixDecompose[V, X, Y](
    capt: PartialArgs[TypeExpr[TypeConstructor[V, _, _], _, _], ○, X],
    pre: Routing[● × ●, Y],
    expr: OpenTypeExpr.LTrimmed[TypeConstructor[V, _, _], X, Y, ●],
  ): PFixDecomposed[V] =
    import expr.inKind2
    import Routing.TraceSndRes.{FstEliminated, SndEliminated, Traced}
    Routing.traceSnd(pre) match
      case FstEliminated(m) =>
        UnhandledCase.raise(s"pfixDecompose($capt, $pre, $expr)")
      case SndEliminated(r) =>
        UnhandledCase.raise(s"pfixDecompose($capt, $pre, $expr)")
      case r: Traced[k1, k2, q1, q2, y1, y2] =>
        summon[Y =:= (y1 × y2)]
        OpenTypeExpr.LTrimmed.ltrimMore(r.tr, expr) match
          case Indeed((args, expr)) =>
            val args1 = args.translate([k, l] => (e: OpenTypeExpr[TypeConstructor[V, _, _], k, l]) => e.unopen)
            PFixDecomposed.Decomposed(Args(r.r, PartialArgs.introFst(capt, args1)), TypeConstructor.PFix(r.m, expr))

  enum FixDecomposed[V]:
    case NothingToFix(constantType: Type[V])
    case CapturedArgs[V, X](
      args: Args[V, ○, X],
      pfix: TypeConstructor.PFix[V, X, ?],
    ) extends FixDecomposed[V]

  enum PFixDecomposed[V]:
    case NothingToFix(result: Type.Fun[V, ●, ●])
    case Decomposed[V, X](
      args: Args[V, ●, X],
      pfix: TypeConstructor.PFix[V, X, ?]
    ) extends PFixDecomposed[V]

  private type Capt[V, K, L] =
    OpenTypeExpr.Capt[TypeConstructor[V, _, _], K, L]

  private def fixDecompose[V, K, X, L](
    cpt: Capt[V, K, X],
    opn: OpenExpr[V, X, L],
  ): Either3[
    K =:= ○,
    Nothing,
    Exists[[Y] =>> (
      PartialArgs[TypeExpr[TypeConstructor[V, _, _], _, _], ○, Y],
      OpenTypeExpr.LTrimmed[TypeConstructor[V, _, _], Y, K, L],
    )],
  ] =
    cpt match
      case OpenTypeExpr.Capt.Total(captured) =>
        Either3.Left(summon[K =:= ○])
      case OpenTypeExpr.Capt.Partial(capture) =>
        capture.exposeCaptured match
          case Left(TypeEq(Refl())) =>
            UnhandledCase.raise(s"fixDecompose($cpt, $opn)")
          case Right(exp) =>
            exp.ev match { case TypeEq(Refl()) =>
              val res = fixWithCapture(exp.captured, exp.route, opn)
              Either3.Right(res)
            }

  private def fixWithCapture[V, X, K, L1, L2, L](
    captured: Tupled[×, TypeConstructor[V, ○, _], X],
    reorg: TransferOpt[X, K, L1, L2],
    opn: OpenExpr[V, L1 × L2, L],
  ): Exists[[Y] =>> (
    PartialArgs[TypeExpr[TypeConstructor[V, _, _], _, _], ○, Y],
    OpenTypeExpr.LTrimmed[TypeConstructor[V, _, _], Y, K, L],
  )] = {
    val c: Tupled[×, TypeExpr[TypeConstructor[V, _, _], ○, _], X] =
      captured.trans[TypeExpr[TypeConstructor[V, _, _], ○, _]](
        [x] => (x: TypeConstructor[V, ○, x]) =>
          given Kind[x] = x.outKind
          TypeExpr.Primitive(x)
      )
    val cArgs: PartialArgs[TypeExpr[TypeConstructor[V, _, _], _, _], ○, X] =
      PartialArgs.fromTupled(
        c,
        properOutKind = [x] => (x: TypeExpr[TypeConstructor[V, _, _], ○, x]) =>
          KindN(x.outKind),
      )
    OpenTypeExpr.ltrim(reorg, opn) match
      case Indeed((captured1, ltrimmed)) =>
        val cArgs1 =
          captured1.translate[TypeExpr[TypeConstructor[V, _, _], _, _]](
            [x, y] => (e: OpenTypeExpr[TypeConstructor[V, _, _], x, y]) =>
              e.unopen
          )
        val capture =
          (cArgs > cArgs1)(
            [j, k, l] => (
              a: PartialArgs[TypeExpr[TypeConstructor[V, _, _], _, _], j, k],
              f: TypeExpr[TypeConstructor[V, _, _], k, l],
            ) =>
              f.applyTo(a)
          )
        Exists((capture, ltrimmed))
  }

  def recCall[V](a: Type[V], b: Type[V]): Type[V] =
    TypeExpr.App(
      TypeConstructor.RecCall(),
      PartialArgs.introBoth(
        PartialArgs(a),
        PartialArgs(b),
      ),
    )

  def abstractType[V](label: V): Type[V] =
    TypeExpr.Primitive(TypeConstructor.AbstractType(label))

  def typeMismatch[V](a: Type[V], b: Type[V]): Type[V] =
    TypeExpr.Primitive(TypeConstructor.TypeMismatch(a, b))

  def forbiddenSelfReference[V](v: V): Type[V] =
    TypeExpr.Primitive(TypeConstructor.ForbiddenSelfRef(v))

  object Pair {
    def unapply[V](t: Type[V]): Option[(Type[V], Type[V])] =
      t match {
        case TypeExpr.App(TypeConstructor.Pair(), args) =>
          PartialArgs.extract(args) match
            case Atom(a) <*> Atom(b) =>
              Some((a, b))
        case _ =>
          None
      }
  }

  object Sum {
    def unapply[V](t: Type[V]): Option[(Type[V], Type[V])] =
      t match {
        case TypeExpr.App(TypeConstructor.Sum(), args) =>
          PartialArgs.extract(args) match
            case Atom(a) <*> Atom(b) =>
              Some((a, b))
        case _ =>
          None
      }
  }

  object RecCall {
    def unapply[V](t: Type[V]): Option[(Type[V], Type[V])] =
      t match {
        case TypeExpr.App(TypeConstructor.RecCall(), args) =>
          PartialArgs.extract(args) match
            case Atom(a) <*> Atom(b) =>
              Some((a, b))
        case _ =>
          None
      }
  }

  object AbstractType {
    def unapply[V](t: Type[V]): Option[V] =
      t match {
        case TypeExpr.Primitive(TypeConstructor.AbstractType(v)) => Some(v)
        case _ => None
      }
  }

  extension [V](t: Type[V]) {
    def compile[==>[_, _], <*>[_, _], One, F[_, _], Q](
      fk: F[○, Q],
      compilePrimitive: [k, l, q] => (F[k, q], TypeConstructor[V, k, l]) => MappedMorphism[==>, F, k, l],
    )(using
      tgt: MonoidalCategory[==>, <*>, One],
      F: MonoidalObjectMap[F, ×, ○, <*>, One],
    ): MappedMorphism[==>, F, ○, ●]  =
      (t: TypeExpr[TypeConstructor[V, _, _], ○, ●]).compile[==>, <*>, One, F, Q](fk, compilePrimitive)
  }

  opaque type Args[V, K, L] = MultiTypeFun[TypeConstructor[V, _, _], K, L]

  object Args {
    private[Type] def apply[V, K, L](
      args: PartialArgs[TypeExpr[TypeConstructor[V, _, _], _, _], K, L],
    ): Args[V, K, L] =
      MultiTypeFun(args)

    private[Type] def apply[V, J, K, L](
      r: Routing[J, K],
      args: PartialArgs[TypeExpr[TypeConstructor[V, _, _], _, _], K, L],
    ): Args[V, J, L] =
      MultiTypeFun(r, args)

    def apply[V](t: Type[V]): Args[V, ○, ●] =
      MultiTypeFun(t)

    def apply[V, K, L](f: Fun[V, K, L]): Args[V, K, L] =
      MultiTypeFun(f)

    def fst[V, K, L, M](f: Fun[V, K, L])(using KindN[K], KindN[M]): Args[V, K × M, L × M] =
      MultiTypeFun.fst(f)

    def snd[V, K, L, M](f: Fun[V, L, M])(using KindN[K], KindN[L]): Args[V, K × L, K × M] =
      MultiTypeFun.snd(f)

    def introFst[V, K, L](f: Fun[V, ○, K])(using KindN[L]): Args[V, L, K × L] =
      MultiTypeFun.introFst(f)

    def introSnd[V, K, L](f: Fun[V, ○, L])(using KindN[K]): Args[V, K, K × L] =
      MultiTypeFun.introSnd(f)

    def introBoth[V](a: Type[V], b: Type[V]): Args[V, ○, ● × ●] =
      MultiTypeFun.introBoth(a, b)

    def introBoth[V, K, L](f: Fun[V, ○, K], g: Fun[V, ○, L]): Args[V, ○, K × L] =
      MultiTypeFun.introBoth(f, g)

    def introBoth[V, K, L](a: Args[V, ○, K], b: Args[V, ○, L]): Args[V, ○, K × L] =
      MultiTypeFun.introBoth(a, b)

    def dup[V, K](using KindN[K]): Args[V, K, K × K] =
      MultiTypeFun.dup

    extension [V, K, L](f: Args[V, K, L]) {
      def feedTo[M](g: Fun[V, L, M]): Fun[V, K, M] =
        f > g

      def inFst[M](using KindN[K], KindN[M]): Args[V, K × M, L × M] =
        f.inFst[M]

      def inSnd[J](using KindN[J], KindN[K]): Args[V, J × K, J × L] =
        f.inSnd[J]
    }
  }

  opaque type Fun[V, K, L] = TypeFun[TypeConstructor[V, _, _], K, L]

  object Fun {
    import TypeFun.{fromExpr, toExpr}

    def lift[V, K, L](tc: TypeConstructor[V, K, L])(using
      Kinds[K],
      Kind[L],
    ): Fun[V, K, L] =
      fromExpr(TypeExpr.lift(tc))

    def unit[V]: Type.Fun[V, ○, ●] =
      fromExpr(Type.unit)

    def int[V]: Type.Fun[V, ○, ●] =
      fromExpr(Type.int)

    def string[V]: Type.Fun[V, ○, ●] =
      fromExpr(Type.string)

    def pair[V]: Type.Fun[V, ● × ●, ●] =
      lift(TypeConstructor.Pair())

    def pair[V](a: Type.Fun[V, ○, ●], b: Type.Fun[V, ○, ●]): Type.Fun[V, ○, ●] =
      fromExpr(Type.pair(toExpr(a), toExpr(b)))

    def pair1[V](a: Type[V]): Type.Fun[V, ●, ●] =
      fromExpr(
        TypeExpr.App(
          TypeConstructor.Pair(),
          PartialArgs.introFst(PartialArgs(a)),
        )
      )

    def pair1[V](a: Type.Fun[V, ○, ●]): Type.Fun[V, ●, ●] =
      pair1(toExpr(a))

    def pair2[V](b: Type[V]): Type.Fun[V, ●, ●] =
      fromExpr(
        TypeExpr.App(
          TypeConstructor.Pair(),
          PartialArgs.introSnd(PartialArgs(b)),
        )
      )

    def pair2[V](b: Type.Fun[V, ○, ●]): Type.Fun[V, ●, ●] =
      pair2(toExpr(b))

    def sum[V]: Type.Fun[V, ● × ●, ●] =
      lift(TypeConstructor.Sum())

    def sum[V](a: Type.Fun[V, ○, ●], b: Type.Fun[V, ○, ●]): Type.Fun[V, ○, ●] =
      fromExpr(Type.sum(toExpr(a), toExpr(b)))

    def sum1[V](a: Type[V]): Type.Fun[V, ●, ●] =
      fromExpr(
        TypeExpr.App(
          TypeConstructor.Sum(),
          PartialArgs.introFst(PartialArgs(a)),
        )
      )

    def sum1[V](a: Type.Fun[V, ○, ●]): Type.Fun[V, ●, ●] =
      sum1(toExpr(a))

    def sum2[V](b: Type[V]): Type.Fun[V, ●, ●] =
      fromExpr(
        TypeExpr.App(
          TypeConstructor.Sum(),
          PartialArgs.introSnd(PartialArgs(b)),
        )
      )

    def fix[V](f: Type.Fun[V, ●, ●]): Type.Fun[V, ○, ●] =
      fromExpr(Type.fix(f))

    def pfix[V, P, X](f: TypeConstructor.PFix[V, P, X]): Fun[V, P, ●] =
      import f.inKind
      lift(f)

    def pfix[V](f: Type.Fun[V, ● × ●, ●]): Type.Fun[V, ●, ●] =
      pfixDecompose(f) match
        case PFixDecomposed.NothingToFix(f) =>
          f
        case PFixDecomposed.Decomposed(args, pf) =>
          args > pfix(pf)

    /** Creates a PFix (parameterized fixed-point) type, if the type arguments `args` match the kinds `P`.
     *  Otherwise, throws an exception.
     */
    def pfixUnsafe[V, P, X](
      f: TypeConstructor.PFix[V, P, X],
      args: Types[V],
    ): Type[V] =
      given KindN[P] = f.g.inKind1
      given KindN[X] = f.g.inKind2
      kindCheck(args, KindN[P]) match
        case Left(msg) =>
          throw IllegalArgumentException(msg)
        case Right(args) =>
          TypeExpr.lift(f: TypeConstructor[V, P, ●])
            .applyTo(args)

    private def kindCheck[V, K](
      ts: Types[V],
      k: KindN[K],
    ): Either[String, PartialArgs[TypeExpr[TypeConstructor[V, _, _], _, _], ○, K]] =
      k match
        case KindN.Type =>
          summon[K =:= ●]
          ts match
            case Types.SingleType(t) =>
              Right(PartialArgs(t)(using summon, k))
            case Types.Product(t, u) =>
              Left(s"Expected a single type, got $t, $u (at ${summon[SourcePos]})")
            case e @ Types.KindMismatch(l, r) =>
              UnhandledCase.raise(s"$e")
        case k: KindN.Prod[k1, k2] =>
          summon[K =:= (k1 × k2)]
          given KindN[k1] = k.k
          given KindN[k2] = k.l
          ts match
            case Types.Product(t, u) =>
              for
                t <- kindCheck(t, k.k)
                u <- kindCheck(u, k.l)
              yield
                PartialArgs.introBoth(t, u)
            case Types.SingleType(t) =>
              Left(s"Expected types of kinds $k, got a single type argument $t")
            case e @ Types.KindMismatch(l, r) =>
              UnhandledCase.raise(s"$e")

    def abstractType[V](name: V): Type.Fun[V, ○, ●] =
      fromExpr(TypeExpr.lift(TypeConstructor.AbstractType(name)))

    def toType[V](f: Fun[V, ○, ●]): Type[V] =
      TypeFun.toExpr(f)

    extension [V, K, L](f: Fun[V, K, L]) {
      def ∘[J](g: Fun[V, J, K]): Fun[V, J, L] =
        f ∘ g

      def >[M](g: Fun[V, L, M]): Fun[V, K, M] =
        g ∘ f

      def ∘[J](r: Routing[J, K]): Fun[V, J, L] =
        f ∘ r

      def applyTo[J](args: Args[V, J, K]): Fun[V, J, L] =
        args > f

      def vmap[W](g: V => W): Fun[W, K, L] =
        f.translate[TypeConstructor[W, _, _]](TypeConstructor.vmap(g))
    }

    extension [V, K](f: Fun[V, K, ●]) {
      def apply(args: Args[V, ○, K]): Type[V] =
        toType(args > f)
    }

    extension [V](f: Fun[V, ●, ●]) {
      def apply(arg: Type[V]): Type[V] =
        (f: TypeFun[TypeConstructor[V, _, _], ●, ●]).apply(arg)
    }
  }
}
