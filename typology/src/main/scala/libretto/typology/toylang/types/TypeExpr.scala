package libretto.typology.toylang.types

import libretto.lambda.{Capture, MappedMorphism, MonoidalCategory, MonoidalObjectMap, Semigroupoid, Shuffle, Tupled, UnhandledCase, Unzippable}
import libretto.lambda.util.{Exists, SourcePos, TypeEq}
import libretto.lambda.util.TypeEq.Refl
import libretto.typology.kinds.*
import libretto.typology.util.Either3

/**
 * Tree-shaped structure that builds up a type
 * (or type constructor, depending on the output kind `L`),
 * from primitive, language specific type constructors.
 *
 * When the input kind `K` is the unit kind [[○]], then this [[TypeExpr]]
 * represents a fully formed type. Otherwise, it represents a type constructor
 * taking additional type parameters of kinds `K`.
 *
 * @tparam TC the primitive, language-specific type constructors, parameterized by input and output kinds
 * @tparam K the kind of additional type parameters of the represented type constructor
 * @tparam L the output kind of the represented type constructor
 */
sealed abstract class TypeExpr[TC[_, _], K, L](using
  val inKind: Kind[K],
  val outKind: OutputKind[L],
) {
  import TypeExpr.*

  def from[J](using ev: J =:= K): TypeExpr[TC, J, L] =
    ev.substituteContra[TypeExpr[TC, _, L]](this)

  def to[M](using ev: L =:= M): TypeExpr[TC, K, M] =
    ev.substituteCo[TypeExpr[TC, K, _]](this)

  def >[M](that: TypeExpr[TC, L, M]): TypeExpr[TC, K, M] =
    that ∘ this

  def ∘[J](that: TypeExpr[TC, J, K]): TypeExpr[TC, J, L] =
    import that.given
    applyTo(PartialArgs(that))

  def after(that: TypeExpr[TC, ○, K]): TypeExpr[TC, ○, L] =
    this ∘ that

  def applyTo[J](
    a: PartialArgs[TypeExpr[TC, _, _], J, K],
  ): TypeExpr[TC, J, L] =
    this match {
      case Primitive(p) =>
        App(p, a)
      case App(op, b) =>
        App(op, (a > b)(absorbArgs[TC]))
    }

  def translate[TC1[_, _]](
    f: [k, l] => TC[k, l] => TC1[k, l]
  ): TypeExpr[TC1, K, L] =
    this match {
      case Primitive(p) =>
        Primitive(f(p))
      case App(op, args) =>
        App(
          f(op),
          args.translate([x, y] => (t: TypeExpr[TC, x, y]) => t.translate(f)),
        )
    }

  def compile[==>[_, _], <*>[_, _], One, F[_, _], Q](
    fk: F[K, Q],
    compilePrimitive: [k, l, q] => (F[k, q], TC[k, l]) => MappedMorphism[==>, F, k, l],
  )(using
    tgt: MonoidalCategory[==>, <*>, One],
    F: MonoidalObjectMap[F, ×, ○, <*>, One],
  ): MappedMorphism[==>, F, K, L] = {

    val go = [k, l, q] => (fkq: F[k, q], t: TypeExpr[TC, k, l]) => {
      val t1 = t.compile[==>, <*>, One, F, q](fkq, compilePrimitive)
      Exists[[r] =>> (q ==> r, F[l, r]), t1.FB]((t1.get(fkq, t1.tgtMap), t1.tgtMap))
    }

    this match
      case Primitive(op) =>
        compilePrimitive(fk, op)
      case App(op, args) =>
        args.foldTranslate[==>, <*>, One, F, Q](F.unit, fk, go) match {
          case Exists.Some((args, fx)) =>
            val op1 = compilePrimitive(fx, op)
            MappedMorphism(fk, args > op1.get(fx, op1.tgtMap), op1.tgtMap)
        }
  }

  def open: Either[
    Closed[TC, K, L],
    Exists[[X] =>> (PartialArgs[Closed[TC, _, _], K, X], TypeExpr.Open[TC, X, L])],
  ] =
    this match
      case Primitive(f) =>
        inKind.properKind match
          case Left(TypeEq(Refl())) =>
            Left(Closed.Impl(f))
          case Right(k) =>
            Right(Exists((PartialArgs.Id()(using k), TypeExpr.Open.primitive(f)(using k))))

      case App(f, args) =>
        args.split[PartialArgs[Closed[TC, _, _], _, _], PartialArgs[TypeExpr.Open[TC, _, _], _, _]](
          [k, l] => (f: TypeExpr[TC, k, l]) => {
            f.open match
              case Left(t) =>
                Exists((PartialArgs(t)(using t.inKind, t.outKind.properKind)), t.outKind.properKind, PartialArgs.Id[TypeExpr.Open[TC, _, _], l]()(using t.outKind.properKind))
                  : Exists[[X] =>> (PartialArgs[Closed[TC, _, _], k, X], ProperKind[X], PartialArgs[TypeExpr.Open[TC, _, _], X, l])]
              case Right(Exists.Some((g, h))) =>
                Exists.Some((g, g.outKind, PartialArgs(h)(using h.inKind.kind, h.outKind.properKind)))
                  : Exists[[X] =>> (PartialArgs[Closed[TC, _, _], k, X], ProperKind[X], PartialArgs[TypeExpr.Open[TC, _, _], X, l])]
          }
        ) match {
          case Exists.Some((args0, args1)) =>
            Right(Exists((PartialArgs.flatten(args0), TypeExpr.Open.App(f, PartialArgs.flatten(args1))(using args0.outKind))))
        }

  def open1: Either[
    Closed[TC, K, L],
    Exists[[X] =>> (Capt[TC, K, X], TypeExpr.Open[TC, X, L])],
  ] =
    this match
      case Primitive(f) =>
        inKind.properKind match
          case Left(TypeEq(Refl())) =>
            Left(Closed.Impl(f))
          case Right(k) =>
            given ProperKind[K] = k
            Right(Exists((Capt.id, TypeExpr.Open.primitive(f))))

      case App(f, args) =>
        args.split[Capt[TC, _, _], PartialArgs[TypeExpr.Open[TC, _, _], _, _]](
          [k, l] => (f: TypeExpr[TC, k, l]) => {
            f.open1 match
              case Left(t) =>
                Exists((Capt.closed(t), t.outKind.properKind, PartialArgs.Id[TypeExpr.Open[TC, _, _], l]()(using t.outKind.properKind)))
                  : Exists[[X] =>> (Capt[TC, k, X], ProperKind[X], PartialArgs[TypeExpr.Open[TC, _, _], X, l])]
              case Right(Exists.Some((g, h))) =>
                Exists.Some((g, h.inKind, PartialArgs(h)(using h.inKind.kind, h.outKind.properKind)))
                  : Exists[[X] =>> (Capt[TC, k, X], ProperKind[X], PartialArgs[TypeExpr.Open[TC, _, _], X, l])]
          }
        ) match {
          case Exists.Some((args0, args1)) =>
            Right(Exists((Capt.foldArgs(args0), TypeExpr.Open.App(f, PartialArgs.flatten(args1))(using args0.outKind))))
        }

  private def absorbArgs[TC[_, _]] =
    [j, k, l] => (
      a: PartialArgs[TypeExpr[TC, _, _], j, k],
      t: TypeExpr[TC, k, l],
    ) => {
      t.applyTo(a)
    }
}

object TypeExpr {

  case class Primitive[TC[_, _], K, L](
    value: TC[K, L],
  )(using
    Kind[K],
    OutputKind[L],
  ) extends TypeExpr[TC, K, L]

  case class App[TC[_, _], K, L, M](
    f: TC[L, M],
    args: PartialArgs[TypeExpr[TC, _, _], K, L],
  )(using
    OutputKind[M],
  ) extends TypeExpr[TC, K, M](using args.inKind)

  given semigroupoid[TC[_, _]]: Semigroupoid[TypeExpr[TC, _, _]] with {
    override def andThen[A, B, C](
      f: TypeExpr[TC, A, B],
      g: TypeExpr[TC, B, C],
    ): TypeExpr[TC, A, C] =
      f > g
  }

  given unzippable[TC[_, _]]: Unzippable[×, TypeExpr[TC, ○, _]] with {
    override def unzip[A, B](
      ab: TypeExpr[TC, ○, A × B],
    ): (TypeExpr[TC, ○, A], TypeExpr[TC, ○, B]) =
      OutputKind.cannotBePair(ab.outKind)
  }

  /** A tree-shaped composition of (proper) type constructors
   * where any embedded primitive type constructor
   * is on at least 1 path between input and output.
   *
   * In other words, there are no fully formed types (`TC[○, K]`) inside.
   */
  sealed trait Open[TC[_, _], K, L](using
    val inKind: ProperKind[K],
    val outKind: OutputKind[L],
  ) {
    def translate[TC1[_, _]](
      f: [k, l] => TC[k, l] => TC1[k, l]
    ): TypeExpr.Open[TC1, K, L] =
      this match {
        // case Open.Primitive(p) =>
        //   Open.Primitive(f(p))
        case Open.App(op, args) =>
          Open.App(
            f(op),
            args.translate([x, y] => (t: TypeExpr.Open[TC, x, y]) => t.translate(f)),
          )
      }

    def asRegular: TypeExpr[TC, K, L] =
      UnhandledCase.raise(s"$this.asRegular")
  }

  object Open {
    given sh: Shuffle[×] = new Shuffle[×]

    // case class Primitive[TC[_, _], K, L](
    //   value: TC[K, L],
    // )(using
    //   ProperKind[K],
    //   OutputKind[L],
    // ) extends TypeExpr.Open[TC, K, L]

    case class App[TC[_, _], K, L, M](
      f: TC[L, M],
      args: PartialArgs[TypeExpr.Open[TC, _, _], K, L],
    )(using
      ProperKind[K],
      OutputKind[M],
    ) extends TypeExpr.Open[TC, K, M]

    def primitive[TC[_, _], K, L](
      op: TC[K, L],
    )(using
      ProperKind[K],
      OutputKind[L],
    ): TypeExpr.Open[TC, K, L] =
      App(op, PartialArgs.Id())

    def ltrim[TC[_, _], J1, J2, K1, K2, L](
      tr: sh.TransferOpt[J1, J2, K1, K2],
      opn: TypeExpr.Open[TC, K1 × K2, L],
    ): Exists[[P] =>> (
      PartialArgs[TypeExpr.Open[TC, _, _], J1, P],
      LTrimmed[TC, P, J2, L],
    )] =
      val (j1, j2) = ProperKind.unpair(tr.asShuffle.invert(opn.inKind))
      given ProperKind[J1] = j1
      given ProperKind[J2] = j2
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
      args: PartialArgs[TypeExpr.Open[TC, _, _], K1 × K2, L],
    ): LTrimmed.PartialArgsRes[TC, J1, J2, L] = {
      import sh.TransferOpt
      import sh.Transfer.{AssocLR, AssocRL, Swap, IX, XI, IXI}
      import PartialArgs.{Id, Lift, Par, Fst, Snd, IntroFst, IntroSnd, IntroBoth}
      import LTrimmed.PartialArgsRes.{Opaque, Translucent}
      import LTrimmed.Args.SemiTransparent.{RPartial, RTotal}

      val (j1, j2) = ProperKind.unpair(tr.asShuffle.invert(ProperKind.fromProd(args.inKind)))
      given ProperKind[J1] = j1
      given ProperKind[J2] = j2

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
            case Fst(f) =>
              UnhandledCase.raise(s"ltrimArgs($tr, $args)")
            case Snd(f) =>
              UnhandledCase.raise(s"ltrimArgs($tr, $args)")
            case IntroFst(_, _) | IntroSnd(_, _) | IntroBoth(_, _) =>
              throw AssertionError(s"Impossible (at ${summon[SourcePos]})") // TODO: use a precise, non-capturing representation of args

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
            case IntroFst(_, _) | IntroSnd(_, _) | IntroBoth(_, _) =>
              throw AssertionError(s"Impossible (at ${summon[SourcePos]})") // TODO: use a precise, non-capturing representation of args

        case a: AssocLR[i1, i2, i3, κ2, κ3] =>
          summon[J1 =:= (i1 × i2)]
          val (i1, i2) = ProperKind.unpair(j1: ProperKind[i1 × i2])
          given ProperKind[i1] = i1
          given ProperKind[i2] = i2
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
                    opq.trimmed.inSnd[i1],
                    RPartial(opq.opaqueBase, TransferOpt.None()),
                  )
                case Translucent(trimmed, translucentBase) =>
                  UnhandledCase.raise(s"ltrimArgs($tr, $args)")
            case IntroFst(_, _) | IntroSnd(_, _) | IntroBoth(_, _) =>
              throw AssertionError(s"Impossible (at ${summon[SourcePos]})") // TODO: use a precise, non-capturing representation of args

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
            case IntroFst(_, _) | IntroSnd(_, _) | IntroBoth(_, _) =>
              throw AssertionError(s"Impossible (at ${summon[SourcePos]})") // TODO: use a precise, non-capturing representation of args

        case IX(g) =>
          UnhandledCase.raise(s"ltrimArgs($tr, $args)")
        case XI(g) =>
          UnhandledCase.raise(s"ltrimArgs($tr, $args)")
        case IXI(g1, g2) =>
          UnhandledCase.raise(s"ltrimArgs($tr, $args)")
    }

    sealed trait LTrimmed[TC[_, _], K1, K2, L](using
      val inKind1: ProperKind[K1],
      val inKind2: ProperKind[K2],
    ) {
      given inKind: ProperKind[K1 × K2] = inKind1 × inKind2

      def translate[TC1[_, _]](
        f: [k, l] => TC[k, l] => TC1[k, l]
      ): TypeExpr.Open.LTrimmed[TC1, K1, K2, L] =
        this match
          case LTrimmed.App(op, args) =>
            LTrimmed.App(f(op), args.translate(f))
          case LTrimmed.RApp(op, args) =>
            LTrimmed.RApp(f(op), args.translate(f))
          // case RApp(op, tr, args) =>
          //   RApp(f(op), tr, args.translate([x, y] => (t: TypeExpr.Open[TC, x, y]) => t.translate(f)))
          // case r @ RAppLTrimmed(op, tr, args) =>
          //   val (k1, k2) = ProperKind.unpair(r.inKind1.kind)
          //   RAppLTrimmed(f(op), tr, args.translate(f))(using k1, k2)
    }

    object LTrimmed {
      case class App[TC[_, _], K1, K2, L, M](
        op: TC[L, M],
        args: LTrimmed.Args[TC, K1, K2, L],
      )(using
        ProperKind[K1],
        ProperKind[K2],
      ) extends LTrimmed[TC, K1, K2, M]

      case class RApp[TC[_, _], K1, K2, L, M](
        op: TC[L, M],
        args: Args.SemiTransparent[TC, K1, K2, L],
      )(using
        ProperKind[K1],
        ProperKind[K2],
      ) extends LTrimmed[TC, K1, K2, M]

      // case class RApp[TC[_, _], K1, K2, Q2, L1, L2, M](
      //   op: TC[L1 × L2, M],
      //   tr: sh.TransferOpt[K1, Q2, L1, L2],
      //   args: PartialArgs[TypeExpr.Open[TC, _, _], K2, Q2],
      // )(using
      //   ProperKind[K1],
      //   ProperKind[K2],
      // ) extends LTrimmed[TC, K1, K2, M]

      // case class RAppLTrimmed[TC[_, _], K1, K2, K3, Q2, L1, L2, M](
      //   op: TC[L1 × L2, M],
      //   tr: sh.TransferOpt[K1, Q2, L1, L2],
      //   args: LTrimmed.Args[TC, K2, K3, Q2],
      // )(using
      //   k1: ProperKind[K1],
      //   k2: ProperKind[K2],
      //   k3: ProperKind[K3],
      // ) extends LTrimmed[TC, K1 × K2, K3, M]

      sealed trait Args[TC[_, _], K1, K2, L] {
        def translate[TC1[_, _]](
          f: [k, l] => TC[k, l] => TC1[k, l]
        ): Args[TC1, K1, K2, L] =
          UnhandledCase.raise(s"$this.translate")
      }

      object Args {
        case class Expr[TC[_, _], K1, K2, L](
          value: TypeExpr.Open.LTrimmed[TC, K1, K2, L],
        ) extends LTrimmed.Args[TC, K1, K2, L]

        case class IXI[TC[_, _], K1, K2, K3, K4, L1, L2](
          a: LTrimmed.Args[TC, K1, K3, L1],
          b: LTrimmed.Args[TC, K2, K4, L2],
        ) extends LTrimmed.Args[TC, K1 × K2, K3 × K4, L1 × L2]

        case class XI[TC[_, _], K1, K2, K3, L1, L2](
          a: PartialArgs[TypeExpr.Open[TC, _, _], K2, L1],
          b: LTrimmed.Args[TC, K1, K3, L2],
        ) extends LTrimmed.Args[TC, K1, K2 × K3, L1 × L2]

        case class |/|[TC[_, _], K1, K2, K3, L1, L2](
          a: LTrimmed.Args[TC, K1, K2, L1],
          b: PartialArgs[TypeExpr.Open[TC, _, _], K3, L2],
        ) extends LTrimmed.Args[TC, K1, K2 × K3, L1 × L2]

        sealed trait SemiTransparent[TC[_, _], K1, K2, L] {
          def translate[TC1[_, _]](
            f: [k, l] => TC[k, l] => TC1[k, l]
          ): SemiTransparent[TC1, K1, K2, L] =
            UnhandledCase.raise(s"$this.translate")
        }
        object SemiTransparent {
          case class RTotal[TC[_, _], K1, K2, L2, M1, M2](
            r: PartialArgs[TypeExpr.Open[TC, _, _], K2, L2],
            tr: sh.TransferOpt[K1, L2, M1, M2],
          ) extends SemiTransparent[TC, K1, K2, M1 × M2]

          case class RPartial[TC[_, _], K1, K2, K3, L2, M1, M2](
            r: LTrimmed.Args[TC, K2, K3, L2],
            tr: sh.TransferOpt[K1, L2, M1, M2],
          ) extends SemiTransparent[TC, K1 × K2, K3, M1 × M2]
        }
      }

      /** The result of left-trimming [[PartialArgs]]. */
      sealed trait PartialArgsRes[TC[_, _], J1, J2, L]

      object PartialArgsRes {
        case class Opaque[TC[_, _], J1, J2, K1, L](
          trimmed: PartialArgs[TypeExpr.Open[TC, _, _], J1, K1],
          opaqueBase: LTrimmed.Args[TC, K1, J2, L],
        ) extends PartialArgsRes[TC, J1, J2, L]

        case class Translucent[TC[_, _], J1, J2, K1, L](
          trimmed: PartialArgs[TypeExpr.Open[TC, _, _], J1, K1],
          translucentBase: Args.SemiTransparent[TC, K1, J2, L],
        ) extends PartialArgsRes[TC, J1, J2, L]
      }
    }
  }

  enum Closed[TC[_, _], K, L]:
    case Impl[TC[_, _], L](value: TC[○, L])(using
      val outKind: OutputKind[L],
    ) extends Closed[TC, ○, L]

    def inKind: Kind[K] =
      this match
        case Impl(_) => summon[Kind[○]]

    def outKind: OutputKind[L]

  enum Capt[TC[_, _], K, L]:
    case Partial(value: Capture[×, TC[○, _], K, L])(using val inKind: ProperKind[K])
    case Total[TC[_, _], L](value: Tupled[×, TC[○, _], L]) extends Capt[TC, ○, L]

  object Capt:
    def id[TC[_, _], K](using ProperKind[K]): Capt[TC, K, K] =
      Capt.Partial(Capture.NoCapture())

    def apply[TC[_, _], L](value: TC[○, L]): Capt[TC, ○, L] =
      Capt.Total(Tupled.atom(value))

    def closed[TC[_, _], K, L](value: Closed[TC, K, L]): Capt[TC, K, L] =
      value match
        case Closed.Impl(value) => Capt(value)

    def extract[TC[_, _], L](a: Capt[TC, ○, L]): Tupled[×, TC[○, _], L] =
      a match
        case p @ Partial(_) => ProperKind.cannotBeUnit(p.inKind)
        case Total(value)   => value

    def extract[TC[_, _], L](a: PartialArgs[Capt[TC, _, _], ○, L]): Tupled[×, TC[○, _], L] =
      PartialArgs
        .extract(a)
        .foldMap([x] => (x: Capt[TC, ○, x]) => extract(x))

    def foldArgs[TC[_, _], K, L](args: PartialArgs[Capt[TC, _, _], K, L]): Capt[TC, K, L] =
      args.inKind.properKind match
        case Left(TypeEq(Refl())) =>
          Total(extract(args))
        case Right(k) =>
          given ProperKind[K] = k
          Partial(foldArgsProper(args))

      // import libretto.lambda.UnhandledCase
      // import PartialArgs.*
      // args match
      //   case Id() => Capt.id
      //   case Lift(f) => UnhandledCase.raise(s"Capt.foldArgs($args)")
      //   case Par(f1, f2) => UnhandledCase.raise(s"Capt.foldArgs($args)")
      //   case Fst(f) => UnhandledCase.raise(s"Capt.foldArgs($args)")
      //   case Snd(f) => UnhandledCase.raise(s"Capt.foldArgs($args)")
      //   case IntroFst(f1, f2) => UnhandledCase.raise(s"Capt.foldArgs($args)")
      //   case IntroSnd(f1, f2) => UnhandledCase.raise(s"Capt.foldArgs($args)")
      //   case IntroBoth(f1, f2) => UnhandledCase.raise(s"Capt.foldArgs($args)")

    private def foldArgsProper[TC[_, _], K, L](
      args: PartialArgs[Capt[TC, _, _], K, L],
    )(using
      k: ProperKind[K],
    ): Capture[×, TC[○, _], K, L] =
      import libretto.lambda.UnhandledCase
      import PartialArgs.{extract => _, *}
      args match
        case Id() => Capture.NoCapture()
        case Lift(f) =>
          f match
            case Capt.Partial(c) => c
            case Capt.Total(value) => ProperKind.cannotBeUnit(k)
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

    // given partialArgsAbstractly[TC[_, _]]: PartialArgs.Abstractly[Capt[TC, _, _]] with
    //   override def id[K]: Capt[TC, K, K] =
    //     Capt.id

    //   override def introFst[K, L, M](
    //     f1: Capt[TC, ○, K],
    //     f2: Capt[TC, L, M],
    //   ): Capt[TC, L, K × M] = ???
}
