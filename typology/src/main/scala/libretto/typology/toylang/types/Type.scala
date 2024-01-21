package libretto.typology.toylang.types

import libretto.lambda.{Shuffle, Tupled, UnhandledCase}
import libretto.lambda.Tupled.*
import libretto.lambda.util.{Exists, TypeEq}
import libretto.lambda.util.TypeEq.Refl
import libretto.typology.kinds.*
import libretto.typology.util.Either3

type Type[V] = TypeExpr[TypeConstructor[V, _, _], ○, ●]

object Type {
  type OpenExpr[V, K, L] = TypeExpr.Open[TypeConstructor[V, _, _], K, L]

  def unit[V]: Type[V]   = TypeExpr.Primitive(TypeConstructor.UnitType())
  def int[V]: Type[V]    = TypeExpr.Primitive(TypeConstructor.IntType())
  def string[V]: Type[V] = TypeExpr.Primitive(TypeConstructor.StringType())

  def pair[V]: TypeExpr[TypeConstructor[V, _, _], ● × ●, ●] =
    TypeExpr.Primitive(TypeConstructor.Pair())

  def pair[V](a: Type[V], b: Type[V]): Type[V] =
    TypeExpr.App(
      TypeConstructor.Pair(),
      PartialArgs.introBoth(
        PartialArgs(a),
        PartialArgs(b),
      ),
    )

  def sum[V]: TypeExpr[TypeConstructor[V, _, _], ● × ●, ●] =
    TypeExpr.Primitive(TypeConstructor.Sum())

  def sum[V](a: Type[V], b: Type[V]): Type[V] =
    TypeExpr.App(
      TypeConstructor.Sum(),
      PartialArgs.introBoth(
        PartialArgs(a),
        PartialArgs(b),
      ),
    )

  def fix[V, K](f: TypeConstructor.Fix[V, K]): Type[V] =
    TypeExpr.Primitive(f)

  def fix[V](f: TypeFun[TypeConstructor[V, _, _], ●, ●]): Type[V] =
    fixDecompose(f) match
      case Either3.Left(t) =>
        t
      case Either3.Middle(n) =>
        n
      case Either3.Right(e @ Exists.Some((args, pf))) =>
        given Kind[e.T] = args.outKind.kind
        TypeFun.toExpr(Type.Fun.pfix(pf).applyTo(args))

  def fixDecompose[V](
    f: TypeFun[TypeConstructor[V, _, _], ●, ●],
  ): Either3[
    Type[V],
    Nothing,
    Exists[[Y] =>> (
      PartialArgs[TypeExpr[TypeConstructor[V, _, _], _, _], ○, Y],
      TypeConstructor.PFix[V, Y, ?],
    )],
  ] =
    f.expr.open1 match
      case Left(t) =>
        UnhandledCase.raise(s"nothing to fix")
      case Right(Exists.Some((cpt, opn))) =>
        fixDecompose(cpt, opn) match
          case Either3.Left(ev) =>
            Either3.Left(f.expr.from(using ev.flip))
          case Either3.Middle(x) =>
            Either3.Middle(x)
          case Either3.Right(Exists.Some((capt, expr))) =>
            import expr.inKind2
            val m = Routing.toMultiplier(f.pre)
            Either3.Right(Exists((capt, TypeConstructor.PFix(m, expr))))

  def pfixDecompose[V](
    f: Type.Fun[V, ● × ●, ●],
  ): Either3[
    Type.Fun[V, ●, ●],
    Nothing,
    Exists[[Y] =>> (
      PartialArgs[TypeExpr[TypeConstructor[V, _, _], _, _], ●, Y],
      TypeConstructor.PFix[V, Y, ?],
    )],
  ] =
    f.expr.open1 match
      case Left(t) =>
        UnhandledCase.raise(s"nothing to fix")
      case Right(Exists.Some((cpt, opn))) =>
        fixDecompose(cpt, opn) match
          case Either3.Left(ev) =>
            Either3.Left(TypeFun(Routing.elim[●], f.expr.from(using ev.flip)))
          case Either3.Middle(x) =>
            Either3.Middle(x)
          case Either3.Right(Exists.Some((capt, expr))) =>
            import expr.inKind2
            import Routing.TraceSndRes.{FstEliminated, SndEliminated, Traced}
            Routing.traceSnd(f.pre) match
              case FstEliminated(m) =>
                UnhandledCase.raise(s"pfixDecompose($f)")
              case SndEliminated(r) =>
                UnhandledCase.raise(s"pfixDecompose($f)")
              case r: Traced[k1, k2, q1, q2, l1, l2] =>
                UnhandledCase.raise(s"pfixDecompose($f)")

  // private type ClosedArgs[V, K, L] =
  //   PartialArgs[TypeExpr.Closed[TypeConstructor[V, _, _], _, _], K, L]

  private type Capt[V, K, L] =
    TypeExpr.Capt[TypeConstructor[V, _, _], K, L]

  import TypeExpr.Open.sh

  private def fixDecompose[V, K, X, L](
    cpt: Capt[V, K, X],
    opn: OpenExpr[V, X, L],
  ): Either3[
    K =:= ○,
    Nothing,
    Exists[[Y] =>> (
      PartialArgs[TypeExpr[TypeConstructor[V, _, _], _, _], ○, Y],
      TypeExpr.Open.LTrimmed[TypeConstructor[V, _, _], Y, K, L],
    )],
  ] =
    cpt match
      case TypeExpr.Capt.Total(captured) =>
        Either3.Left(summon[K =:= ○])
      case TypeExpr.Capt.Partial(capture) =>
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
    reorg: sh.TransferOpt[X, K, L1, L2],
    opn: OpenExpr[V, L1 × L2, L],
  ): Exists[[Y] =>> (
    PartialArgs[TypeExpr[TypeConstructor[V, _, _], _, _], ○, Y],
    TypeExpr.Open.LTrimmed[TypeConstructor[V, _, _], Y, K, L],
  )] = {
    val c: Tupled[×, TypeExpr[TypeConstructor[V, _, _], ○, _], X] =
      captured.trans[TypeExpr[TypeConstructor[V, _, _], ○, _]](
        [x] => (x: TypeConstructor[V, ○, x]) =>
          given OutputKind[x] = x.outKind
          TypeExpr.Primitive(x)
      )
    val cArgs: PartialArgs[TypeExpr[TypeConstructor[V, _, _], _, _], ○, X] =
      PartialArgs.fromTupled(
        c,
        properOutKind = [x] => (x: TypeExpr[TypeConstructor[V, _, _], ○, x]) =>
          x.outKind.properKind,
      )
    TypeExpr.Open.ltrim(reorg, opn) match
      case Exists.Some((captured1, ltrimmed)) =>
        val cArgs1 =
          captured1.translate[TypeExpr[TypeConstructor[V, _, _], _, _]](
            [x, y] => (e: TypeExpr.Open[TypeConstructor[V, _, _], x, y]) =>
              e.asRegular
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

  type Fun[V, K, L] = TypeFun[TypeConstructor[V, _, _], K, L]

  object Fun {
    import TypeFun.{fromExpr, toExpr}

    def unit[V]: Type.Fun[V, ○, ●] =
      fromExpr(Type.unit)

    def int[V]: Type.Fun[V, ○, ●] =
      fromExpr(Type.int)

    def string[V]: Type.Fun[V, ○, ●] =
      fromExpr(Type.string)

    def pair[V]: Type.Fun[V, ● × ●, ●] =
      fromExpr(Type.pair)

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
      fromExpr(TypeExpr.Primitive(TypeConstructor.Sum()))

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

    def pfix[V, P, X](f: TypeConstructor.PFix[V, P, X])(using Kind[P]): Type.Fun[V, P, ●] =
      fromExpr(TypeExpr.Primitive(f))

    def pfix[V](f: Type.Fun[V, ● × ●, ●]): Type.Fun[V, ●, ●] =
      pfixDecompose(f) match
        case Either3.Left(f) => f
        case Either3.Middle(value) => value
        case Either3.Right(e @ Exists.Some((args, pf))) =>
          given Kind[e.T] = args.outKind.kind
          TypeFun(Routing.id[●], pfix(pf).applyTo(args))

    def abstractType[V](name: V): Type.Fun[V, ○, ●] =
      fromExpr(TypeExpr.Primitive(TypeConstructor.AbstractType(name)))
  }
}
