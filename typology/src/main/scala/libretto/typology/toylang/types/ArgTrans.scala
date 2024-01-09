package libretto.typology.toylang.types

import libretto.lambda.{MonoidalCategory, MonoidalObjectMap, Semigroupoid, Tupled, UnhandledCase}
import libretto.lambda.util.{Exists, TypeEq}
import libretto.lambda.util.TypeEq.Refl
import libretto.typology.kinds._

/** Represents partial type arguments.
 *
 * When fed to type constructor `T` of kind `L -> M`,
 * the resulting kind of the type constructor becomes `K -> M`.
 *
 * The representation is unique:
  there is only 1 way to represent any given partial type arguments as [[ArgTrans]].
 *
 * A type argument might be provided fully, as `F[○, k]` (for some kind `k`);
 * or itself require further type arguments. For example,
 * `F[● × ●, ●]` represents a binary type constructor, such as `Either`, `Map`, etc.
 * It "reduces" the request for a type argument to a request for two type arguments:
 * When a type is required and we provide, say, `Either`, it leads to requiring 2 more types (the arguments of `Either`).
 *
 * The unit-kinded (○) inputs are coalesced with a neighbor input.
 * For example, there will be `K` instead of `K × ○`.
 * Consequently, the only input kind containing `○` is `○` itself.
 *
 * @tparam K the kind of the remaining type arguments (i.e. arguments to be provided later)
 * @tparam L the kind after transforming (some of the) type arguments
 * @tparam F the type of type arguments, parameterized by input and output kind
 */
sealed trait ArgTrans[F[_, _], K, L] {
  import ArgTrans.*

  given inKind: Kind[K]
  given outKind: ProperKind[L]

  def from[J](using ev: J =:= K): ArgTrans[F, J, L] =
    ev.substituteContra[ArgTrans[F, _, L]](this)

  def to[M](using ev: L =:= M): ArgTrans[F, K, M] =
    ev.substituteCo[ArgTrans[F, K, _]](this)

  def >[M](that: ArgTrans[F, L, M])(
    absorbL: [j, k, l] => (ArgTrans[F, j, k], F[k, l]) => F[j, l],
  ): ArgTrans[F, K, M] =
    this match
      case Id() => that
      case thiz: Proper[f, k, l] => (that composeProper thiz)(absorbL)

  def composeProper[J](that: Proper[F, J, K])(
    absorbL: [j, k, l] => (ArgTrans[F, j, k], F[k, l]) => F[j, l],
  ): Proper[F, J, L]

  def introFst[M](f1: ArgTrans.Proper[F, ○, M])(using ProperKind[K]): ArgTrans.Proper[F, K, M × L] =
    IntroFst(f1, this)

  def introSnd[M](f2: ArgTrans.Proper[F, ○, M])(using ProperKind[K]): ArgTrans.Proper[F, K, L × M] =
    IntroSnd(this, f2)

  def translate[G[_, _]](h: [x, y] => F[x, y] => G[x, y]): ArgTrans[G, K, L] =
    this match
      case Id()                  => Id()
      case thiz: Proper[f, k, l] => thiz.translateProper(h)

  def fold(using F: MonoidalCategory[F, ×, ○]): F[K, L] =
    this match
      case Id()                  => F.id
      case thiz: Proper[f, k, l] => thiz.foldProper

  def foldTranslate[G[_, _]](h: [x, y] => F[x, y] => G[x, y])(using
    G: MonoidalCategory[G, ×, ○],
  ): G[K, L] =
    translate(h).fold

  def foldTranslate[G[_, _], <*>[_, _], One, Φ[_, _], Q](
    φ0: Φ[○, One],
    φ: Φ[K, Q],
    h: [k, l, q] => (Φ[k, q], F[k, l]) => Exists[[r] =>> (G[q, r], Φ[l, r])],
  )(using
    G: MonoidalCategory[G, <*>, One],
    Φ: MonoidalObjectMap[Φ, ×, ○, <*>, One],
  ): Exists[[R] =>> (G[Q, R], Φ[L, R])] =
    this match
      case Id() =>
        Exists((G.id, φ))
      case Lift(f) =>
        h(φ, f)
      case Par(f1, f2) =>
        UnhandledCase.raise(s"${this}.foldTranslate")
      case Fst(f) =>
        UnhandledCase.raise(s"${this}.foldTranslate")
      case Snd(f) =>
        UnhandledCase.raise(s"${this}.foldTranslate")
      case IntroFst(f1, f2) =>
        f1.foldTranslate[G, <*>, One, Φ, One](φ0, φ0, h) match
          case Exists.Some((g1, φ1)) =>
            f2.foldTranslate[G, <*>, One, Φ, Q](φ0, φ, h) match
              case Exists.Some((g2, φ2)) =>
                Exists((g2 > G.introFst(g1), Φ.pair(φ1, φ2)))
      case IntroSnd(f1, f2) =>
        UnhandledCase.raise(s"${this}.foldTranslate")
      case IntroBoth(f1, f2) =>
        UnhandledCase.raise(s"${this}.foldTranslate")

  def extract(using ev: K =:= ○): Tupled[×, F[○, _], L] =
    ArgTrans.extract(this.from[○](using ev.flip))
}

object ArgTrans {
  case class Id[F[_, _], K]()(using
    val kind: ProperKind[K],
  ) extends ArgTrans[F, K, K] {
    override def inKind: Kind[K] = kind.kind
    override def outKind: ProperKind[K] = kind

    override def composeProper[J](that: Proper[F, J, K])(
      absorbL: [j, k, l] => (ArgTrans[F, j, k], F[k, l]) => F[j, l],
    ): Proper[F, J, K] =
      that
  }

  sealed trait Proper[F[_, _], K, L] extends ArgTrans[F, K, L] {
    override def from[J](using ev: J =:= K): ArgTrans.Proper[F, J, L] =
      ev.substituteContra[ArgTrans.Proper[F, _, L]](this)

    override def to[M](using ev: L =:= M): ArgTrans.Proper[F, K, M] =
      ev.substituteCo[ArgTrans.Proper[F, K, _]](this)

    def inFst[M](using ProperKind[K], ProperKind[M]): ArgTrans[F, K × M, L × M] =
      ArgTrans.fst(this)

    def inSnd[J](using ProperKind[J], ProperKind[K]): ArgTrans[F, J × K, J × L] =
      ArgTrans.snd(this)

    def translateProper[G[_, _]](h: [x, y] => F[x, y] => G[x, y]): ArgTrans.Proper[G, K, L] =
      this match
        case w @ Lift(f)           => import w.given; Lift(h(f))
        case p @ Par(f1, f2)       => import p.given; Par(f1.translateProper(h), f2.translateProper(h))
        case f @ Fst(f1)           => Fst(f1.translateProper(h))(using f.inKind1, f.kind2)
        case s @ Snd(f2)           => Snd(f2.translateProper(h))(using s.kind1, s.inKind2)
        case i @ IntroFst(f1, f2)  => import i.given; IntroFst(f1.translateProper(h), f2.translate(h))
        case i @ IntroSnd(f1, f2)  => import i.given; IntroSnd(f1.translate(h), f2.translateProper(h))
        case i @ IntroBoth(f1, f2) => IntroBoth(f1.translateProper(h), f2.translateProper(h))

    def foldProper(using F: MonoidalCategory[F, ×, ○]): F[K, L] =
      this match
        case Lift(f)            => f
        case Par(f1, f2)        => F.par(f1.foldProper, f2.foldProper)
        case f: Fst[f, k, l, m] => F.fst[k, l, m](f.f.foldProper)
        case f: Snd[f, k, l, m] => F.snd[k, l, m](f.f.foldProper)
        case IntroFst(f1, f2)   => f2.fold > F.introFst(f1.foldProper)
        case IntroSnd(f1, f2)   => f1.fold > F.introSnd(f2.foldProper)
        case IntroBoth(f1, f2)  => f1.foldProper > F.introSnd(f2.foldProper)
  }

  case class Lift[F[_, _], K, L](f: F[K, L])(using
    k: Kind[K],
    val outputKind: OutputKind[L],
  ) extends ArgTrans.Proper[F, K, L] {
    override def inKind: Kind[K] = k
    override def outKind: ProperKind[L] = outputKind.properKind

    override def composeProper[J](that: Proper[F, J, K])(
      absorbL: [j, k, l] => (ArgTrans[F, j, k], F[k, l]) => F[j, l],
    ): Proper[F, J, L] =
      import that.given
      Lift(absorbL[J, K, L](that, f))
  }

  case class Par[F[_, _], K1, K2, L1, L2](
    f1: ArgTrans.Proper[F, K1, L1],
    f2: ArgTrans.Proper[F, K2, L2],
  )(using
    val inKind1: ProperKind[K1],
    val inKind2: ProperKind[K2],
  ) extends ArgTrans.Proper[F, K1 × K2, L1 × L2] {
    override def inKind: Kind[K1 × K2] = (ProperKind[K1] × ProperKind[K2]).kind
    override def outKind: ProperKind[L1 × L2] = f1.outKind × f2.outKind

    override def composeProper[J](that: Proper[F, J, K1 × K2])(
      absorbL: [j, k, l] => (ArgTrans[F, j, k], F[k, l]) => F[j, l],
    ): Proper[F, J, L1 × L2] =
      UnhandledCase.raise(s"$that > $this")
  }

  case class Fst[F[_, _], K, L, M](
    f: ArgTrans.Proper[F, K, L],
  )(using
    val inKind1: ProperKind[K],
    val kind2: ProperKind[M]
  ) extends ArgTrans.Proper[F, K × M, L × M] {
    override def inKind: Kind[K × M] = (ProperKind[K] × ProperKind[M]).kind
    override def outKind: ProperKind[L × M] = f.outKind × ProperKind[M]

    override def composeProper[J](that: Proper[F, J, K × M])(
      absorbL: [j, k, l] => (ArgTrans[F, j, k], F[k, l]) => F[j, l],
    ): Proper[F, J, L × M] =
      UnhandledCase.raise(s"$that > $this")
  }

  case class Snd[F[_, _], K, L, M](
    f: ArgTrans.Proper[F, L, M],
  )(using
    val kind1: ProperKind[K],
    val inKind2: ProperKind[L],
  ) extends ArgTrans.Proper[F, K × L, K × M] {
    override def inKind: Kind[K × L] = (ProperKind[K] × ProperKind[L]).kind
    override def outKind: ProperKind[K × M] = ProperKind[K] × f.outKind

    def in1Kind: ProperKind[K] = ProperKind[K]
    def in2Kind: ProperKind[L] = ProperKind[L]
    def out2Kind: ProperKind[M] = f.outKind

    override def composeProper[J](that: Proper[F, J, K × L])(
      absorbL: [j, k, l] => (ArgTrans[F, j, k], F[k, l]) => F[j, l],
    ): Proper[F, J, K × M] =
      that match
        case Lift(f) =>
          UnhandledCase.raise(s"$that")
        case Par(f1, f2) =>
          UnhandledCase.raise(s"$that")
        case Fst(f) =>
          UnhandledCase.raise(s"$that")
        case Snd(f) =>
          UnhandledCase.raise(s"$that")
        case IntroFst(f1, f2) =>
          ArgTrans.introFst(f1, (f2 > f)(absorbL))
        case IntroSnd(f1, f2) =>
          UnhandledCase.raise(s"$that")
        case IntroBoth(f1, f2) =>
          UnhandledCase.raise(s"$that")
  }

  case class IntroFst[F[_, _], K, L, M](
    f1: ArgTrans.Proper[F, ○, K],
    f2: ArgTrans[F, L, M],
  )(using
    val inKindProper: ProperKind[L],
  ) extends ArgTrans.Proper[F, L, K × M] {
    override def inKind: Kind[L] = ProperKind[L].kind
    override def outKind: ProperKind[K × M] = f1.outKind × f2.outKind

    override def composeProper[J](that: Proper[F, J, L])(
      absorbL: [j, k, l] => (ArgTrans[F, j, k], F[k, l]) => F[j, l],
    ): Proper[F, J, K × M] =
      ArgTrans.introFst(f1, (that > f2)(absorbL))
  }

  case class IntroSnd[F[_, _], K, L, M](
    f1: ArgTrans[F, K, L],
    f2: ArgTrans.Proper[F, ○, M],
  )(using
    val inKindProper: ProperKind[K],
  ) extends ArgTrans.Proper[F, K, L × M] {
    override def inKind: Kind[K] = ProperKind[K].kind
    override def outKind: ProperKind[L × M] = f1.outKind × f2.outKind

    override def composeProper[J](that: Proper[F, J, K])(
      absorbL: [j, k, l] => (ArgTrans[F, j, k], F[k, l]) => F[j, l],
    ): Proper[F, J, L × M] =
      ArgTrans.introSnd((that > f1)(absorbL), f2)
  }

  case class IntroBoth[F[_, _], K, L](
    f1: ArgTrans.Proper[F, ○, K],
    f2: ArgTrans.Proper[F, ○, L],
  ) extends ArgTrans.Proper[F, ○, K × L] {
    override def inKind: Kind[○] = summon[Kind[○]]
    override def outKind: ProperKind[K × L] = f1.outKind × f2.outKind

    override def composeProper[J](that: Proper[F, J, ○])(
      absorbL: [j, k, l] => (ArgTrans[F, j, k], F[k, l]) => F[j, l],
    ): Proper[F, J, K × L] =
      UnhandledCase.raise(s"$that > $this")
  }

  def apply[F[_, _], K: Kind, L: OutputKind](f: F[K, L]): ArgTrans.Proper[F, K, L] =
    lift(f)

  def lift[F[_, _], K: Kind, L: OutputKind](f: F[K, L]): ArgTrans.Proper[F, K, L] =
    Lift(f)

  def par[F[_, _], K1: ProperKind, K2: ProperKind, L1, L2](
    f1: ArgTrans[F, K1, L1],
    f2: ArgTrans[F, K2, L2],
  ): ArgTrans[F, K1 × K2, L1 × L2] =
    (f1, f2) match {
      case (i1 @ Id()            , i2 @ Id())             => Id()(using i1.kind × i2.kind)
      case (i1 @ Id()            , f2: Proper[f, k2, l2]) => Snd(f2)
      case (f1: Proper[f, k1, l1], i2 @ Id())             => Fst(f1)
      case (f1: Proper[f, k1, l1], f2: Proper[g, k2, l2]) => Par(f1, f2)
    }

  def fst[F[_, _], K: ProperKind, L, M: ProperKind](
    f: ArgTrans[F, K, L],
  ): ArgTrans[F, K × M, L × M] =
    f match
      case f: Proper[f, k, l] => Fst(f)
      case Id()               => Id[F, K × M]()

  def snd[F[_, _], K: ProperKind, L: ProperKind, M](
    f: ArgTrans[F, L, M],
  ): ArgTrans[F, K × L, K × M] =
    f match
      case f: Proper[f, l, m] => Snd(f)
      case Id()               => Id[F, K × L]()

  def introFst[F[_, _], K, L, M](
    f1: ArgTrans[F, ○, K],
    f2: ArgTrans[F, L, M],
  ): ArgTrans.Proper[F, L, K × M] =
    f2.inKind.properKind match
      case Left(TypeEq(Refl())) => IntroBoth(proper(f1), proper(f2))
      case Right(l)             => IntroFst(proper(f1), f2)(using l)

  def introFst[F[_, _], K, L: ProperKind](
    f1: ArgTrans[F, ○, K],
  ): ArgTrans.Proper[F, L, K × L] =
    IntroFst(proper(f1), Id())

  def introSnd[F[_, _], K, L, M](
    f1: ArgTrans[F, K, L],
    f2: ArgTrans[F, ○, M],
  ): ArgTrans.Proper[F, K, L × M] =
    f1.inKind.properKind match
      case Left(TypeEq(Refl())) => IntroBoth(proper(f1), proper(f2))
      case Right(k)             => IntroSnd(f1, proper(f2))(using k)

  def introSnd[F[_, _], K: ProperKind, L](
    f2: ArgTrans[F, ○, L],
  ): ArgTrans.Proper[F, K, K × L] =
    IntroSnd(Id(), proper(f2))

  def introBoth[F[_, _], K, L](
    f1: ArgTrans[F, ○, K],
    f2: ArgTrans[F, ○, L],
  ): ArgTrans[F, ○, K × L] =
    IntroBoth(proper(f1), proper(f2))

  def proper[F[_, _], L](f: ArgTrans[F, ○, L]): ArgTrans.Proper[F, ○, L] =
    f match
      case f: Proper[f, o, l] => f
      case i @ Id() => ProperKind.cannotBeUnit(i.kind)

  def extract[F[_, _], L](f: ArgTrans[F, ○, L]): Tupled[×, F[○, _], L] =
    f match
      case Lift(f)              => Tupled.atom(f)
      case IntroBoth(f1, f2)    => extract(f1) zip extract(f2)
      case i @ Id()             => ProperKind.cannotBeUnit(i.kind)
      case i @ IntroFst(f1, f2) => ProperKind.cannotBeUnit(i.inKindProper)
      case i @ IntroSnd(f1, f2) => ProperKind.cannotBeUnit(i.inKindProper)
      case _: Par[f, k1, k2, l1, l2] => throw new AssertionError("Impossible: ○ != k1 × k2")
      case _: Fst[f, k, l, m]        => throw new AssertionError("Impossible: ○ != k × m")
      case _: Snd[f, k, l, m]        => throw new AssertionError("Impossible: ○ != k × l")

}
