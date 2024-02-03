package libretto.typology.toylang.types

import libretto.lambda.{Capture, Tupled, UnhandledCase}
import libretto.lambda.util.{Exists, SourcePos, TypeEq}
import libretto.lambda.util.TypeEq.Refl
import libretto.typology.kinds.*
import libretto.typology.types.{kindShuffle => sh}

/** A tree-shaped composition of (proper) type constructors
 * where any embedded primitive type constructor
 * is on at least 1 path between input and output.
 *
 * In other words, there are no fully formed types (`TC[○, K]`) inside.
 */
sealed trait OpenTypeExpr[TC[_, _], K, L](using
  val inKind: KindN[K],
  val outKind: Kind[L],
) {
  def translate[TC1[_, _]](
    f: [k, l] => TC[k, l] => TC1[k, l]
  ): OpenTypeExpr[TC1, K, L] =
    this match {
      case OpenTypeExpr.App(op, args) =>
        OpenTypeExpr.App(
          f(op),
          args.translate([x, y] => (t: OpenTypeExpr[TC, x, y]) => t.translate(f)),
        )
    }

  def unopen: TypeExpr[TC, K, L] =
    this match
      case OpenTypeExpr.App(op, args) =>
        TypeExpr.App(op, args.translate(OpenTypeExpr.unopen[TC]))
}

object OpenTypeExpr {

  case class App[TC[_, _], K, L, M](
    f: TC[L, M],
    args: PartialArgs[OpenTypeExpr[TC, _, _], K, L],
  )(using
    KindN[K],
    Kind[M],
  ) extends OpenTypeExpr[TC, K, M]

  def primitive[TC[_, _], K, L](
    op: TC[K, L],
  )(using
    KindN[K],
    Kind[L],
  ): OpenTypeExpr[TC, K, L] =
    App(op, PartialArgs.Id())

  def cannotBeConstant[TC[_, _]]: [L] => OpenTypeExpr[TC, ○, L] => Nothing =
    [L] => (t: OpenTypeExpr[TC, ○, L]) => KindN.cannotBeUnit(t.inKind)

  def translate[TC[_, _], TC1[_, _]](
    f: [k, l] => TC[k, l] => TC1[k, l],
  ): [k, l] => OpenTypeExpr[TC, k, l] => OpenTypeExpr[TC1, k, l] =
    [k, l] => (x: OpenTypeExpr[TC, k, l]) => x.translate(f)

  def unopen[TC[_, _]]: [k, l] => OpenTypeExpr[TC, k, l] => TypeExpr[TC, k, l] =
    [k, l] => (e: OpenTypeExpr[TC, k, l]) => e.unopen

  def open[TC[_, _], K, L](
    t: TypeExpr[TC, K, L],
  ): Either[
    Closed[TC, K, L],
    Exists[[X] =>> (Capt[TC, K, X], OpenTypeExpr[TC, X, L])],
  ] =
    import t.given
    t match
      case TypeExpr.Primitive(f) =>
        summon[K =:= ○]
        Left(Closed.Impl(f))

      case TypeExpr.App(f, args) =>
        args.split[Capt[TC, _, _], PartialArgs[OpenTypeExpr[TC, _, _], _, _]](
          [k, l] => (f: TypeExpr[TC, k, l]) => {
            open(f) match
              case Left(t) =>
                Exists((Capt.closed(t), KindN(t.outKind), PartialArgs.Id[OpenTypeExpr[TC, _, _], l]()(using KindN(t.outKind))))
                  : Exists[[X] =>> (Capt[TC, k, X], KindN[X], PartialArgs[OpenTypeExpr[TC, _, _], X, l])]
              case Right(Exists.Some((g, h))) =>
                Exists.Some((g, h.inKind, PartialArgs(h)(using Kinds(h.inKind), KindN(h.outKind))))
                  : Exists[[X] =>> (Capt[TC, k, X], KindN[X], PartialArgs[OpenTypeExpr[TC, _, _], X, l])]
          }
        ) match {
          case Exists.Some((args0, args1)) =>
            Right(Exists((Capt.foldArgs(args0), OpenTypeExpr.App(f, PartialArgs.flatten(args1))(using args0.outKind))))
        }

  def ltrim[TC[_, _], J1, J2, K1, K2, L](
    tr: sh.TransferOpt[J1, J2, K1, K2],
    opn: OpenTypeExpr[TC, K1 × K2, L],
  ): Exists[[P] =>> (
    PartialArgs[OpenTypeExpr[TC, _, _], J1, P],
    LTrimmed[TC, P, J2, L],
  )] =
    val (j1, j2) = KindN.unpair(tr.asShuffle.invert(opn.inKind))
    given KindN[J1] = j1
    given KindN[J2] = j2
    opn match
      case App(op, args) =>
        import LTrimmed.PartialArgsRes.{Opaque, Translucent}
        ltrimArgs(tr, args) match
          case Opaque(trimmed, base) =>
            Exists((trimmed, LTrimmed.App(op, base)(using trimmed.outKind)))
          case Translucent(trimmed, base) =>
            Exists((trimmed, LTrimmed.RApp(op, base)(using trimmed.outKind)))

  private def ltrimArgs[TC[_, _], J1, J2, K1, K2, L](
    tr: sh.TransferOpt[J1, J2, K1, K2],
    args: PartialArgs[OpenTypeExpr[TC, _, _], K1 × K2, L],
  ): LTrimmed.PartialArgsRes[TC, J1, J2, L] = {
    import sh.TransferOpt
    import sh.Transfer.{AssocLR, AssocRL, Swap, IX, XI, IXI}
    import PartialArgs.{Id, Lift, Par, Fst, Snd, IntroFst, IntroSnd, IntroBoth}
    import LTrimmed.PartialArgsRes.{Opaque, Translucent}
    import LTrimmed.Args.SemiTransparent.{RPartial, RTotal}

    val (j1, j2) = KindN.unpair(tr.asShuffle.invert(Kinds.nonEmpty(args.inKind)))
    given KindN[J1] = j1
    given KindN[J2] = j2

    tr match
      case TransferOpt.None() =>
        summon[J1 =:= K1]
        summon[J2 =:= K2]
        args match
          case Id() =>
            summon[(K1 × K2) =:= L]
            Translucent[TC, J1, J2, J1, L](
              Id(),
              RTotal(Id()(using j2), TransferOpt.None()),
            )
          case Lift(f) =>
            ltrim(TransferOpt.None(), f) match
              case Exists.Some((cap, base)) =>
                Opaque(cap, LTrimmed.Args.Expr(base))
          case Par(f1, f2) =>
            UnhandledCase.raise(s"ltrimArgs($tr, $args)")
          case f: Fst[f, k1, l1, k2] =>
            summon[L =:= (l1 × K2)]
            Translucent[TC, J1, J2, l1, L](f.f, RTotal[TC, l1, J2, J2, l1, J2](Id(), TransferOpt.None()))
          case Snd(f) =>
            Translucent[TC, J1, J2, J1, L](Id(), RTotal(f, TransferOpt.None()))
          case IntroFst(f1, _) =>
            PartialArgs.cannotBeConstant(f1, OpenTypeExpr.cannotBeConstant[TC])
          case IntroSnd(_, f2) =>
            PartialArgs.cannotBeConstant(f2, OpenTypeExpr.cannotBeConstant[TC])

      case Swap() =>
        args match
          case Id() =>
            UnhandledCase.raise(s"ltrimArgs($tr, $args)")
          case Lift(f) =>
            UnhandledCase.raise(s"ltrimArgs($tr, $args)")
          case Par(f1, f2) =>
            UnhandledCase.raise(s"ltrimArgs($tr, $args)")
          case Fst(f) =>
            UnhandledCase.raise(s"ltrimArgs($tr, $args)")
          case Snd(f) =>
            UnhandledCase.raise(s"ltrimArgs($tr, $args)")
          case IntroFst(f1, _) =>
            PartialArgs.cannotBeConstant(f1, OpenTypeExpr.cannotBeConstant[TC])
          case IntroSnd(_, f2) =>
            PartialArgs.cannotBeConstant(f2, OpenTypeExpr.cannotBeConstant[TC])

      case a: AssocLR[i1, i2, i3, κ2, κ3] =>
        summon[J1 =:= (i1 × i2)]
        val (i1, i2) = KindN.unpair(j1: KindN[i1 × i2])
        given KindN[i1] = i1
        given KindN[i2] = i2
        args match
          case Id() =>
            UnhandledCase.raise(s"ltrimArgs($tr, $args)")
          case Lift(f) =>
            UnhandledCase.raise(s"ltrimArgs($tr, $args)")
          case Par(f1, f2) =>
            UnhandledCase.raise(s"ltrimArgs($tr, $args)")
          case Fst(f) =>
            UnhandledCase.raise(s"ltrimArgs($tr, $args)")
          case Snd(f) =>
            ltrimArgs(a.g, f) match
              case opq: Opaque[tc, i2, i3, x1, l2] =>
                Translucent[TC, J1, J2, i1 × x1, L](
                  opq.extruded.inSnd[i1],
                  RPartial(opq.opaqueBase, TransferOpt.None()),
                )
              case Translucent(extruded, translucentBase) =>
                UnhandledCase.raise(s"ltrimArgs($tr, $args)")
          case IntroFst(f1, _) =>
            PartialArgs.cannotBeConstant(f1, OpenTypeExpr.cannotBeConstant[TC])
          case IntroSnd(_, f2) =>
            PartialArgs.cannotBeConstant(f2, OpenTypeExpr.cannotBeConstant[TC])

      case AssocRL(g) =>
        args match
          case Id() =>
            UnhandledCase.raise(s"ltrimArgs($tr, $args)")
          case Lift(f) =>
            UnhandledCase.raise(s"ltrimArgs($tr, $args)")
          case Par(f1, f2) =>
            UnhandledCase.raise(s"ltrimArgs($tr, $args)")
          case Fst(f) =>
            UnhandledCase.raise(s"ltrimArgs($tr, $args)")
          case Snd(f) =>
            UnhandledCase.raise(s"ltrimArgs($tr, $args)")
          case IntroFst(f1, _) =>
            PartialArgs.cannotBeConstant(f1, OpenTypeExpr.cannotBeConstant[TC])
          case IntroSnd(_, f2) =>
            PartialArgs.cannotBeConstant(f2, OpenTypeExpr.cannotBeConstant[TC])

      case IX(g) =>
        UnhandledCase.raise(s"ltrimArgs($tr, $args)")
      case XI(g) =>
        UnhandledCase.raise(s"ltrimArgs($tr, $args)")
      case IXI(g1, g2) =>
        UnhandledCase.raise(s"ltrimArgs($tr, $args)")
  }

  sealed trait LTrimmed[TC[_, _], K1, K2, L](using
    val inKind1: KindN[K1],
    val inKind2: KindN[K2],
  ) {
    given inKind: KindN[K1 × K2] = inKind1 × inKind2

    def translate[TC1[_, _]](
      f: [k, l] => TC[k, l] => TC1[k, l]
    ): OpenTypeExpr.LTrimmed[TC1, K1, K2, L] =
      this match
        case LTrimmed.App(op, args) =>
          LTrimmed.App(f(op), args.translate(f))
        case LTrimmed.RApp(op, args) =>
          LTrimmed.RApp(f(op), args.translate(f))
  }

  object LTrimmed {
    case class App[TC[_, _], K1, K2, L, M](
      op: TC[L, M],
      args: LTrimmed.Args[TC, K1, K2, L],
    )(using
      KindN[K1],
      KindN[K2],
    ) extends LTrimmed[TC, K1, K2, M]

    case class RApp[TC[_, _], K1, K2, L, M](
      op: TC[L, M],
      args: LTrimmed.Args.SemiTransparent[TC, K1, K2, L],
    )(using
      KindN[K1],
      KindN[K2],
    ) extends LTrimmed[TC, K1, K2, M]

    def ltrimMore[TC[_, _], K1, K2, K3, Q2, Q3, L](
      tr: sh.TransferOpt[K2, K3, Q2, Q3],
      expr: LTrimmed[TC, K1, Q2 × Q3, L]
    ): Exists[[P2] =>> (
      PartialArgs[OpenTypeExpr[TC, _, _], K2, P2],
      LTrimmed[TC, K1 × P2, K3, L],
    )] =
      given KindN[K3] = KindN.unpair(tr.asShuffle.invert(expr.inKind2))._2
      expr match
        case App(op, args) =>
          UnhandledCase.raise(s"ltrimMore($tr, $expr)")
        case RApp(op, args) =>
          Args.SemiTransparent.ltrimMore(tr, args) match
            case Exists.Some((extruded, args)) =>
              Exists((extruded, RApp(op, args)(using expr.inKind1 × extruded.outKind)))

    sealed trait Args[TC[_, _], K1, K2, L] {
      import Args.*

      def translate[TC1[_, _]](
        f: [k, l] => TC[k, l] => TC1[k, l]
      ): Args[TC1, K1, K2, L] =
        this match
          case Expr(value) =>
            Expr(value.translate(f))
          case IXI(a, b) =>
            UnhandledCase.raise(s"$this.translate")
          case XI(a, b) =>
            UnhandledCase.raise(s"$this.translate")
          case |/|(a, b) =>
            UnhandledCase.raise(s"$this.translate")

    }

    object Args {
      case class Expr[TC[_, _], K1, K2, L](
        value: OpenTypeExpr.LTrimmed[TC, K1, K2, L],
      ) extends LTrimmed.Args[TC, K1, K2, L]

      case class IXI[TC[_, _], K1, K2, K3, K4, L1, L2](
        a: LTrimmed.Args[TC, K1, K3, L1],
        b: LTrimmed.Args[TC, K2, K4, L2],
      ) extends LTrimmed.Args[TC, K1 × K2, K3 × K4, L1 × L2]

      case class XI[TC[_, _], K1, K2, K3, L1, L2](
        a: PartialArgs[OpenTypeExpr[TC, _, _], K2, L1],
        b: LTrimmed.Args[TC, K1, K3, L2],
      ) extends LTrimmed.Args[TC, K1, K2 × K3, L1 × L2]

      case class |/|[TC[_, _], K1, K2, K3, L1, L2](
        a: LTrimmed.Args[TC, K1, K2, L1],
        b: PartialArgs[OpenTypeExpr[TC, _, _], K3, L2],
      ) extends LTrimmed.Args[TC, K1, K2 × K3, L1 × L2]

      sealed trait SemiTransparent[TC[_, _], K1, K2, L] {
        import SemiTransparent.*

        def translate[TC1[_, _]](
          f: [k, l] => TC[k, l] => TC1[k, l]
        ): SemiTransparent[TC1, K1, K2, L] =
          val g = OpenTypeExpr.translate[TC, TC1](f)
          this match
            case RTotal(r, tr)   => RTotal(r.translate(g), tr)
            case RPartial(r, tr) => RPartial(r.translate(f), tr)

      }
      object SemiTransparent {
        case class RTotal[TC[_, _], K1, K2, L2, M1, M2](
          r: PartialArgs[OpenTypeExpr[TC, _, _], K2, L2],
          tr: sh.TransferOpt[K1, L2, M1, M2],
        ) extends SemiTransparent[TC, K1, K2, M1 × M2]

        case class RPartial[TC[_, _], K1, K2, K3, L2, M1, M2](
          r: LTrimmed.Args[TC, K2, K3, L2],
          tr: sh.TransferOpt[K1, L2, M1, M2],
        ) extends SemiTransparent[TC, K1 × K2, K3, M1 × M2]

        def ltrimMore[TC[_, _], K1, K2, K3, P2, P3, L](
          tr: sh.TransferOpt[K2, K3, P2, P3],
          args: SemiTransparent[TC, K1, P2 × P3, L]
        ): Exists[[Q2] =>> (
          PartialArgs[OpenTypeExpr[TC, _, _], K2, Q2],
          SemiTransparent[TC, K1 × Q2, K3, L],
        )] =
          args match
            case RTotal(r, tr2) =>
              import PartialArgsRes.{Opaque, Translucent}
              ltrimArgs(tr, r) match
                case Opaque(extruded, opaqueBase) =>
                  Exists((extruded, RPartial(opaqueBase, tr2)))
                case x @ Translucent(extruded, translucentBase) =>
                  UnhandledCase.raise(s"$x")
            case RPartial(r, tr) =>
              UnhandledCase.raise(s"ltrimMore($tr, $args)")
      }
    }

    /** The result of left-trimming [[PartialArgs]]. */
    sealed trait PartialArgsRes[TC[_, _], J1, J2, L]

    object PartialArgsRes {
      case class Opaque[TC[_, _], J1, J2, K1, L](
        extruded: PartialArgs[OpenTypeExpr[TC, _, _], J1, K1],
        opaqueBase: LTrimmed.Args[TC, K1, J2, L],
      ) extends PartialArgsRes[TC, J1, J2, L]

      case class Translucent[TC[_, _], J1, J2, K1, L](
        extruded: PartialArgs[OpenTypeExpr[TC, _, _], J1, K1],
        translucentBase: Args.SemiTransparent[TC, K1, J2, L],
      ) extends PartialArgsRes[TC, J1, J2, L]
    }
  }

  enum Closed[TC[_, _], K, L]:
    case Impl[TC[_, _], L](value: TC[○, L])(using
      val outKind: Kind[L],
    ) extends Closed[TC, ○, L]

    def inKind: Kinds[K] =
      this match
        case Impl(_) => summon[Kinds[○]]

    def outKind: Kind[L]

  enum Capt[TC[_, _], K, L]:
    case Partial(value: Capture[×, TC[○, _], K, L])(using val inKind: KindN[K])
    case Total[TC[_, _], L](value: Tupled[×, TC[○, _], L]) extends Capt[TC, ○, L]

  object Capt:
    def id[TC[_, _], K](using KindN[K]): Capt[TC, K, K] =
      Capt.Partial(Capture.NoCapture())

    def apply[TC[_, _], L](value: TC[○, L]): Capt[TC, ○, L] =
      Capt.Total(Tupled.atom(value))

    def closed[TC[_, _], K, L](value: Closed[TC, K, L]): Capt[TC, K, L] =
      value match
        case Closed.Impl(value) => Capt(value)

    def extract[TC[_, _], L](a: Capt[TC, ○, L]): Tupled[×, TC[○, _], L] =
      a match
        case p @ Partial(_) => KindN.cannotBeUnit(p.inKind)
        case Total(value)   => value

    def extract[TC[_, _], L](a: PartialArgs[Capt[TC, _, _], ○, L]): Tupled[×, TC[○, _], L] =
      PartialArgs
        .extract(a)
        .foldMap([x] => (x: Capt[TC, ○, x]) => extract(x))

    def foldArgs[TC[_, _], K, L](args: PartialArgs[Capt[TC, _, _], K, L]): Capt[TC, K, L] =
      args.inKind.nonEmpty match
        case Left(TypeEq(Refl())) =>
          Total(extract(args))
        case Right(k) =>
          given KindN[K] = k
          Partial(foldArgsProper(args))

    private def foldArgsProper[TC[_, _], K, L](
      args: PartialArgs[Capt[TC, _, _], K, L],
    )(using
      k: KindN[K],
    ): Capture[×, TC[○, _], K, L] =
      import libretto.lambda.UnhandledCase
      import PartialArgs.{extract => _, *}
      args match
        case Id() => Capture.NoCapture()
        case Lift(f) =>
          f match
            case Capt.Partial(c) => c
            case Capt.Total(value) => KindN.cannotBeUnit(k)
        case Par(f1, f2) => UnhandledCase.raise(s"Capt.foldArgs($args)")
        case Fst(f) => UnhandledCase.raise(s"Capt.foldArgs($args)")
        case Snd(f) => UnhandledCase.raise(s"Capt.foldArgs($args)")
        case IntroFst(f1, f2) =>
          Capture.CaptureFst(
            extract(f1),
            foldArgsProper(f2),
          )
        case IntroSnd(f1, f2) => UnhandledCase.raise(s"Capt.foldArgs($args)")
        case IntroBoth(f1, f2) => UnhandledCase.raise(s"Capt.foldArgs($args)")
}
