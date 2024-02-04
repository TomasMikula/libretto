package libretto.typology.types

import libretto.lambda.{MonoidalCategory, MonoidalObjectMap, Projection, Tupled, UnhandledCase}
import libretto.lambda.util.{Exists, TypeEq}
import libretto.lambda.util.TypeEq.Refl
import libretto.typology.kinds._
import libretto.typology.types.kindShuffle.{~⚬, Transfer}

/** Represents partial type arguments.
 *
 * When fed to a type constructor of kind `L -> M`,
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
 * @tparam L the kind of full type arguments (of which only _some_ might be delivered by this instance)
 * @tparam F the type of type arguments, parameterized by input and output kind
 */
sealed trait PartialArgs[F[_, _], K, L] {
  import PartialArgs.*

  given inKind: Kinds[K]
  given outKind: KindN[L]

  def from[J](using ev: J =:= K): PartialArgs[F, J, L] =
    ev.substituteContra[PartialArgs[F, _, L]](this)

  def to[M](using ev: L =:= M): PartialArgs[F, K, M] =
    ev.substituteCo[PartialArgs[F, K, _]](this)

  def >[M](that: PartialArgs[F, L, M])(
    absorbL: [j, k, l] => (PartialArgs[F, j, k], F[k, l]) => F[j, l],
  ): PartialArgs[F, K, M] =
    this match
      case Id() => that
      case thiz: Proper[f, k, l] => (that composeProper thiz)(absorbL)

  def composeProper[J](that: Proper[F, J, K])(
    absorbL: [j, k, l] => (PartialArgs[F, j, k], F[k, l]) => F[j, l],
  ): Proper[F, J, L]

  def inFst[Y](using KindN[K], KindN[Y]): PartialArgs[F, K × Y, L × Y] =
    fst(this)

  def inSnd[X](using KindN[X], KindN[K]): PartialArgs[F, X × K, X × L] =
    snd(this)

  def introFst[M](f1: PartialArgs.Proper[F, ○, M])(using KindN[K]): PartialArgs.Proper[F, K, M × L] =
    IntroFst(f1, this)

  def introSnd[M](f2: PartialArgs.Proper[F, ○, M])(using KindN[K]): PartialArgs.Proper[F, K, L × M] =
    IntroSnd(this, f2)

  def translate[G[_, _]](h: [x, y] => F[x, y] => G[x, y]): PartialArgs[G, K, L] =
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
        summon[K =:= ○]
        val ev: (Q =:= One) = Φ.uniqueOutputType(φ, φ0)
        f1.foldTranslate[G, <*>, One, Φ, One](φ0, φ0, h) match
          case Exists.Some((g1, φ1)) =>
            f2.foldTranslate[G, <*>, One, Φ, One](φ0, φ0, h) match
              case Exists.Some((g2, φ2)) =>
                ev match { case TypeEq(Refl()) =>
                  Exists((g1 > G.introSnd(g2), Φ.pair(φ1, φ2)))
                }

  def extract(using ev: K =:= ○): Tupled[×, F[○, _], L] =
    PartialArgs.extract(this.from[○](using ev.flip))

  def split[G[_, _], H[_, _]](
    f: [k, l] => F[k, l] => Exists[[x] =>> (G[k, x], KindN[x], H[x, l])],
  ): Exists[[X] =>> (PartialArgs[G, K, X], PartialArgs[H, X, L])] =
    this match
      case Id() =>
        Exists((Id(), Id()))
      case l @ Lift(p) =>
        import l.given
        f(p) match
          case Exists.Some((g, x, h)) =>
            Exists((Lift(g)(using summon, x), Lift(h)(using Kinds(x))))
      case Par(f1, f2) =>
        UnhandledCase.raise(s"$this.split")
      case Fst(f) =>
        UnhandledCase.raise(s"$this.split")
      case Snd(f) =>
        UnhandledCase.raise(s"$this.split")
      case i @ IntroFst(f1, f2) =>
        import i.given
        (f1.split(f), f2.split(f)) match
          case (Exists.Some((g1, h1)), Exists.Some((g2, h2))) =>
            Exists((IntroFst(proper(g1), g2), par(h1, h2)(using g1.outKind, g2.outKind)))
      case IntroSnd(f1, f2) =>
        UnhandledCase.raise(s"$this.split")
      case IntroBoth(f1, f2) =>
        (f1.split(f), f2.split(f)) match
          case (Exists.Some((g1, h1)), Exists.Some((g2, h2))) =>
            Exists((introBoth(g1, g2), par(h1, h2)(using g1.outKind, g2.outKind)))

  def project[M](p: Projection[×, L, M]): Exists[[X] =>> (Projection[×, K, X], PartialArgs[F, X, M])] =
    p match
      case Projection.Id() => Exists((Projection.Id(), this))
      case p: Projection.Proper[pr, l, m] => projectProper(p)

  protected def projectProper[M](p: Projection.Proper[×, L, M]): Exists[[X] =>> (Projection[×, K, X], PartialArgs[F, X, M])] =
    UnhandledCase.raise(s"$this.projectProper($p)")

  def dup(using
    Kind[L],
  ): Exists[[KK] =>> Exists[[X] =>> (Multipliers[K, KK], KK ~⚬ X, PartialArgs[F, X, L × L])]] =
    this match
      case i @ Id() =>
        Multipliers.dup(i.kind) match
          case Exists.Some((m, s)) =>
            Exists(Exists((m, s, Id())))
      case l @ Lift(f) =>
        l.inKind.nonEmpty match
          case Left(TypeEq(Refl())) =>
            Exists(Exists((Multipliers.id[○], ~⚬.id, IntroBoth(Lift(f), Lift(f)))))
          case Right(k) =>
            given KindN[K] = k
            Multipliers.dup(k) match
              case Exists.Some((m, s)) =>
                Exists(Exists((m, s, Par(Lift(f), Lift(f)))))
      case Par(f1, f2) =>
        UnhandledCase.raise(s"$this.dup")
      case Fst(f) =>
        UnhandledCase.raise(s"$this.dup")
      case Snd(f) =>
        UnhandledCase.raise(s"$this.dup")
      case IntroFst(f1, f2) =>
        UnhandledCase.raise(s"$this.dup")
      case IntroSnd(f1, f2) =>
        UnhandledCase.raise(s"$this.dup")
      case IntroBoth(f1, f2) =>
        UnhandledCase.raise(s"$this.dup")


  def multiply[LL](
    m: Multiplier[×, L, LL],
  )(using
    Kind[L]
  ): Exists[[KK] =>> Exists[[X] =>> (Multipliers[K, KK], KK ~⚬ X, PartialArgs[F, X, LL])]] =
    m match
      case Multiplier.Id() =>
        Exists(Exists(Multipliers.id, ~⚬.id, this))
      case Multiplier.Dup(m1, m2) =>
        this.dup match
          case Exists.Some(Exists.Some((m0, s0, a))) =>
            a.multiply(Multipliers.Par(Multipliers.Single(m1), Multipliers.Single(m2))) match
              case Exists.Some(Exists.Some((m1, s1, a1))) =>
                m1.preShuffle(s0) match
                  case Exists.Some((m1, s0)) =>
                    Exists.Some(Exists.Some((m0 > m1, s0 > s1, a1)))

  def multiply[LL](
    m: Multipliers[L, LL],
  ): Exists[[KK] =>> Exists[[X] =>> (Multipliers[K, KK], KK ~⚬ X, PartialArgs[F, X, LL])]] =
    m match
      case s @ Multipliers.Single(m) =>
        this.multiply(m)(using s.inKind)
      case m @ Multipliers.Par(m1, m2) =>
        import m1.outKind
        this match
          case Id() => Exists(Exists((m, ~⚬.id, Id()(using m.outKind))))
          case Lift(f) =>
            UnhandledCase.raise(s"$this.multiply($m)")
          case Par(f1, f2) =>
            UnhandledCase.raise(s"$this.multiply($m)")
          case f @ Fst(f1) =>
            import f.given
            import m2.outKind
            f1.multiply(m1) match
              case Exists.Some(y @ Exists.Some((m1, s1, a1))) =>
                given KindN[y.T] = s1(m1(f.inKind1))
                Exists(Exists((Multipliers.Par(m1.proper, m2), ~⚬.fst(s1), a1.inFst)))
          case f @ Snd(f2) =>
            import f.given
            f2.multiply(m2) match
              case Exists.Some(y @ Exists.Some((m2, s2, a2))) =>
                given KindN[y.T] = s2(m2(f.inKind2))
                Exists(Exists((Multipliers.Par(m1, m2.proper), ~⚬.snd(s2), a2.inSnd)))
          case IntroFst(f1, f2) =>
            (f1.multiply(m1), f2.multiply(m2)) match
              case (Exists.Some(Exists.Some((m1, s1, a1))), Exists.Some(Exists.Some((m2, s2, a2)))) =>
                Multipliers.proveId(m1) match
                  case TypeEq(Refl()) =>
                    s1.proveId(Kinds.unitIsNotPair) match
                      case TypeEq(Refl()) =>
                        Exists(Exists((m2, s2, PartialArgs.introFst(a1, a2))))
          case IntroSnd(f1, f2) =>
            (f1.multiply(m1), f2.multiply(m2)) match
              case (Exists.Some(Exists.Some((m1, s1, a1))), Exists.Some(Exists.Some((m2, s2, a2)))) =>
                Multipliers.proveId(m2) match
                  case TypeEq(Refl()) =>
                    s2.proveId(Kinds.unitIsNotPair) match
                      case TypeEq(Refl()) =>
                        Exists(Exists((m1, s1, PartialArgs.introSnd(a1, a2))))
          case IntroBoth(f1, f2) =>
            (f1.multiply(m1), f2.multiply(m2)) match
              case (Exists.Some(Exists.Some((m1, s1, a1))), Exists.Some(Exists.Some((m2, s2, a2)))) =>
                Multipliers.proveId(m1) match
                  case TypeEq(Refl()) =>
                    Multipliers.proveId(m2) match
                      case TypeEq(Refl()) =>
                        s1.proveId(Kinds.unitIsNotPair) match
                          case TypeEq(Refl()) =>
                            s2.proveId(Kinds.unitIsNotPair) match
                              case TypeEq(Refl()) =>
                                Exists(Exists((Multipliers.id, ~⚬.id, introBoth(a1, a2))))

      case Multipliers.None =>
        KindN.cannotBeUnit(this.outKind)

  def shuffle[M](s: L ~⚬ M): Exists[[X] =>> (K ~⚬ X, PartialArgs[F, X, M])] =
    s match
      case ~⚬.Id() =>
        Exists((~⚬.id, this))
      case ~⚬.Bimap(par) =>
        UnhandledCase.raise(s"$this.shuffle($s)")
      case x: ~⚬.Xfer[l1, l2, x1, x2, m1, m2] =>
        PartialArgs.biShuffle[F, K, l1, l2, x1, x2](this, x.f1, x.f2) match
          case Exists.Some((s, f)) =>
            PartialArgs.transfer(f, x.transfer) match
              case Exists.Some((t, f)) =>
                Exists((s > t, f))
}

object PartialArgs {
  case class Id[F[_, _], K]()(using
    val kind: KindN[K],
  ) extends PartialArgs[F, K, K] {
    override def inKind: Kinds[K] = Kinds(kind)
    override def outKind: KindN[K] = kind

    override def composeProper[J](that: Proper[F, J, K])(
      absorbL: [j, k, l] => (PartialArgs[F, j, k], F[k, l]) => F[j, l],
    ): Proper[F, J, K] =
      that
  }

  sealed trait Proper[F[_, _], K, L] extends PartialArgs[F, K, L] {
    override def from[J](using ev: J =:= K): PartialArgs.Proper[F, J, L] =
      ev.substituteContra[PartialArgs.Proper[F, _, L]](this)

    override def to[M](using ev: L =:= M): PartialArgs.Proper[F, K, M] =
      ev.substituteCo[PartialArgs.Proper[F, K, _]](this)

    def translateProper[G[_, _]](h: [x, y] => F[x, y] => G[x, y]): PartialArgs.Proper[G, K, L] =
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
    k: Kinds[K],
    // val outputKind: OutputKind[L],
    override val outKind: KindN[L],
  ) extends PartialArgs.Proper[F, K, L] {
    override def inKind: Kinds[K] = k
    // override def outKind: ProperKind[L] = outputKind.properKind

    override def composeProper[J](that: Proper[F, J, K])(
      absorbL: [j, k, l] => (PartialArgs[F, j, k], F[k, l]) => F[j, l],
    ): Proper[F, J, L] =
      import that.given
      Lift(absorbL[J, K, L](that, f))
  }

  case class Par[F[_, _], K1, K2, L1, L2](
    f1: PartialArgs.Proper[F, K1, L1],
    f2: PartialArgs.Proper[F, K2, L2],
  )(using
    val inKind1: KindN[K1],
    val inKind2: KindN[K2],
  ) extends PartialArgs.Proper[F, K1 × K2, L1 × L2] {
    override def inKind: Kinds[K1 × K2] = Kinds(KindN[K1] × KindN[K2])
    override def outKind: KindN[L1 × L2] = f1.outKind × f2.outKind

    override def composeProper[J](that: Proper[F, J, K1 × K2])(
      absorbL: [j, k, l] => (PartialArgs[F, j, k], F[k, l]) => F[j, l],
    ): Proper[F, J, L1 × L2] =
      UnhandledCase.raise(s"$that > $this")
  }

  case class Fst[F[_, _], K, L, M](
    f: PartialArgs.Proper[F, K, L],
  )(using
    val inKind1: KindN[K],
    val kind2: KindN[M]
  ) extends PartialArgs.Proper[F, K × M, L × M] {
    override def inKind: Kinds[K × M] = Kinds(KindN[K] × KindN[M])
    override def outKind: KindN[L × M] = f.outKind × KindN[M]

    override def composeProper[J](that: Proper[F, J, K × M])(
      absorbL: [j, k, l] => (PartialArgs[F, j, k], F[k, l]) => F[j, l],
    ): Proper[F, J, L × M] =
      UnhandledCase.raise(s"$that > $this")
  }

  case class Snd[F[_, _], K, L, M](
    f: PartialArgs.Proper[F, L, M],
  )(using
    val kind1: KindN[K],
    val inKind2: KindN[L],
  ) extends PartialArgs.Proper[F, K × L, K × M] {
    override def inKind: Kinds[K × L] = Kinds(KindN[K] × KindN[L])
    override def outKind: KindN[K × M] = KindN[K] × f.outKind

    def in1Kind: KindN[K] = KindN[K]
    def in2Kind: KindN[L] = KindN[L]
    def out2Kind: KindN[M] = f.outKind

    override def composeProper[J](that: Proper[F, J, K × L])(
      absorbL: [j, k, l] => (PartialArgs[F, j, k], F[k, l]) => F[j, l],
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
          PartialArgs.introFst(f1, (f2 > f)(absorbL))
        case IntroSnd(f1, f2) =>
          UnhandledCase.raise(s"$that")
        case IntroBoth(f1, f2) =>
          PartialArgs.introBoth(f1, (f2 > f)(absorbL))
  }

  case class IntroFst[F[_, _], K, L, M](
    f1: PartialArgs.Proper[F, ○, K],
    f2: PartialArgs[F, L, M],
  )(using
    val inKindProper: KindN[L],
  ) extends PartialArgs.Proper[F, L, K × M] {
    override def inKind: Kinds[L] = Kinds(KindN[L])
    override def outKind: KindN[K × M] = f1.outKind × f2.outKind

    override def composeProper[J](that: Proper[F, J, L])(
      absorbL: [j, k, l] => (PartialArgs[F, j, k], F[k, l]) => F[j, l],
    ): Proper[F, J, K × M] =
      PartialArgs.introFst(f1, (that > f2)(absorbL))
  }

  case class IntroSnd[F[_, _], K, L, M](
    f1: PartialArgs[F, K, L],
    f2: PartialArgs.Proper[F, ○, M],
  )(using
    val inKindProper: KindN[K],
  ) extends PartialArgs.Proper[F, K, L × M] {
    override def inKind: Kinds[K] = Kinds(KindN[K])
    override def outKind: KindN[L × M] = f1.outKind × f2.outKind

    override def composeProper[J](that: Proper[F, J, K])(
      absorbL: [j, k, l] => (PartialArgs[F, j, k], F[k, l]) => F[j, l],
    ): Proper[F, J, L × M] =
      PartialArgs.introSnd((that > f1)(absorbL), f2)
  }

  case class IntroBoth[F[_, _], K, L](
    f1: PartialArgs.Proper[F, ○, K],
    f2: PartialArgs.Proper[F, ○, L],
  ) extends PartialArgs.Proper[F, ○, K × L] {
    override def inKind: Kinds[○] = summon[Kinds[○]]
    override def outKind: KindN[K × L] = f1.outKind × f2.outKind

    override def composeProper[J](that: Proper[F, J, ○])(
      absorbL: [j, k, l] => (PartialArgs[F, j, k], F[k, l]) => F[j, l],
    ): Proper[F, J, K × L] =
      UnhandledCase.raise(s"$that > $this")
  }

  def apply[F[_, _], K: Kinds, L: KindN](f: F[K, L]): PartialArgs.Proper[F, K, L] =
    lift(f)

  def lift[F[_, _], K: Kinds, L: KindN](f: F[K, L]): PartialArgs.Proper[F, K, L] =
    Lift(f)

  def par[F[_, _], K1: KindN, K2: KindN, L1, L2](
    f1: PartialArgs[F, K1, L1],
    f2: PartialArgs[F, K2, L2],
  ): PartialArgs[F, K1 × K2, L1 × L2] =
    (f1, f2) match {
      case (i1 @ Id()            , i2 @ Id())             => Id()(using i1.kind × i2.kind)
      case (i1 @ Id()            , f2: Proper[f, k2, l2]) => Snd(f2)
      case (f1: Proper[f, k1, l1], i2 @ Id())             => Fst(f1)
      case (f1: Proper[f, k1, l1], f2: Proper[g, k2, l2]) => Par(f1, f2)
    }

  def fst[F[_, _], K: KindN, L, M: KindN](
    f: PartialArgs[F, K, L],
  ): PartialArgs[F, K × M, L × M] =
    f match
      case f: Proper[f, k, l] => Fst(f)
      case Id()               => Id[F, K × M]()

  def snd[F[_, _], K: KindN, L: KindN, M](
    f: PartialArgs[F, L, M],
  ): PartialArgs[F, K × L, K × M] =
    f match
      case f: Proper[f, l, m] => Snd(f)
      case Id()               => Id[F, K × L]()

  def introFst[F[_, _], K, L, M](
    f1: PartialArgs[F, ○, K],
    f2: PartialArgs[F, L, M],
  ): PartialArgs.Proper[F, L, K × M] =
    f2.inKind.nonEmpty match
      case Left(TypeEq(Refl())) => IntroBoth(proper(f1), proper(f2))
      case Right(l)             => IntroFst(proper(f1), f2)(using l)

  def introFst[F[_, _], K, L: KindN](
    f1: PartialArgs[F, ○, K],
  ): PartialArgs.Proper[F, L, K × L] =
    IntroFst(proper(f1), Id())

  def introSnd[F[_, _], K, L, M](
    f1: PartialArgs[F, K, L],
    f2: PartialArgs[F, ○, M],
  ): PartialArgs.Proper[F, K, L × M] =
    f1.inKind.nonEmpty match
      case Left(TypeEq(Refl())) => IntroBoth(proper(f1), proper(f2))
      case Right(k)             => IntroSnd(f1, proper(f2))(using k)

  def introSnd[F[_, _], K: KindN, L](
    f2: PartialArgs[F, ○, L],
  ): PartialArgs.Proper[F, K, K × L] =
    IntroSnd(Id(), proper(f2))

  def introBoth[F[_, _], K, L](
    f1: PartialArgs[F, ○, K],
    f2: PartialArgs[F, ○, L],
  ): PartialArgs.Proper[F, ○, K × L] =
    IntroBoth(proper(f1), proper(f2))

  def proper[F[_, _], L](f: PartialArgs[F, ○, L]): PartialArgs.Proper[F, ○, L] =
    f match
      case f: Proper[f, o, l] => f
      case i @ Id() => KindN.cannotBeUnit(i.kind)

  def extract[F[_, _], L](f: PartialArgs[F, ○, L]): Tupled[×, F[○, _], L] =
    f match
      case Lift(f)              => Tupled.atom(f)
      case IntroBoth(f1, f2)    => extract(f1) zip extract(f2)
      case i @ Id()             => KindN.cannotBeUnit(i.kind)
      case i @ IntroFst(f1, f2) => KindN.cannotBeUnit(i.inKindProper)
      case i @ IntroSnd(f1, f2) => KindN.cannotBeUnit(i.inKindProper)
      case _: Par[f, k1, k2, l1, l2] => throw new AssertionError("Impossible: ○ != k1 × k2")
      case _: Fst[f, k, l, m]        => throw new AssertionError("Impossible: ○ != k × m")
      case _: Snd[f, k, l, m]        => throw new AssertionError("Impossible: ○ != k × l")

  def fromTupled[F[_, _], L](
    fl: Tupled[×, F[○, _], L],
    properOutKind: [l] => F[○, l] => KindN[l],
  ): PartialArgs[F, ○, L] =
    fl.foldMapWith[PartialArgs[F, ○, _]](
      map = [x] => (fx: F[○, x]) =>
        given KindN[x] = properOutKind(fx)
        lift(fx),
      zip = [x, y] => (x: PartialArgs[F, ○, x], y: PartialArgs[F, ○, y]) =>
        introBoth(x, y)
    )

  def cannotBeConstant[F[_, _], L](
    args: PartialArgs[F, ○, L],
    lemma: [l] => F[○, l] => Nothing,
  ): Nothing =
    cannotBeConstant(args, lemma, summon)

  private def cannotBeConstant[F[_, _], K, L](
    args: PartialArgs[F, K, L],
    lemma: [l] => F[○, l] => Nothing,
    ev: K =:= ○,
  ): Nothing =
    args match
      case i @ Id()                  => ev match { case TypeEq(Refl()) => KindN.cannotBeUnit(i.kind) }
      case Lift(f)                   => ev match { case TypeEq(Refl()) => lemma(f) }
      case p: IntroFst[f, k, l, m]   => ev match { case TypeEq(Refl()) => KindN.cannotBeUnit(p.inKindProper) }
      case p: IntroSnd[f, k, l, m]   => ev match { case TypeEq(Refl()) => KindN.cannotBeUnit(p.inKindProper) }
      case p: Par[f, k1, k2, l1, l2] => KindN.cannotBeUnit(ev.substituteCo(p.inKind1 × p.inKind2))
      case p: Fst[f, k1, k2, l1]     => KindN.cannotBeUnit(ev.substituteCo(p.inKind1 × p.kind2))
      case p: Snd[f, k1, k2, l2]     => KindN.cannotBeUnit(ev.substituteCo(p.kind1 × p.inKind2))
      case IntroBoth(f1, f2)         => cannotBeConstant(f1, lemma, ev)

  def unpair[F[_, _], L1, L2](
    a: PartialArgs[F, ○, L1 × L2],
  ): (PartialArgs[F, ○, L1], PartialArgs[F, ○, L2]) =
    a match
      case IntroBoth(f1, f2) =>
        (f1, f2)
      case i: Id[f, k] =>
        throw AssertionError("Unreachable case")
      case Lift(f) =>
        throw AssertionError("Unreachable case")
      case Par(f1, f2) =>
        throw AssertionError("Unreachable case")
      case Fst(f) =>
        throw AssertionError("Unreachable case")
      case Snd(f) =>
        throw AssertionError("Unreachable case")
      case IntroFst(f1, f2) =>
        throw AssertionError("Unreachable case")
      case IntroSnd(f1, f2) =>
        throw AssertionError("Unreachable case")

  def flatten[F[_, _], K, L](a: PartialArgs[PartialArgs[F, _, _], K, L]): PartialArgs[F, K, L] =
    a match
      case i @ Id() =>
        import i.given
        Id()
      case Lift(f) =>
        f
      case p @ Par(f1, f2) =>
        import p.given
        par(flatten(f1), flatten(f2))
      case f: Fst[f, k, l, m] =>
        import f.given
        fst[F, k, l, m](flatten(f.f))
      case Snd(f2) =>
        UnhandledCase.raise(s"PartialArgs.flatten($a)")
      case i @ IntroFst(f1, f2) =>
        import i.given
        IntroFst(proper(flatten(f1)), flatten(f2))
      case IntroSnd(f1, f2) =>
        UnhandledCase.raise(s"PartialArgs.flatten($a)")
      case IntroBoth(f1, f2) =>
        UnhandledCase.raise(s"PartialArgs.flatten($a)")

  private def biShuffle[F[_, _], K, L1, L2, M1, M2](
    a: PartialArgs[F, K, L1 × L2],
    s1: L1 ~⚬ M1,
    s2: L2 ~⚬ M2,
  ): Exists[[X] =>> (K ~⚬ X, PartialArgs[F, X, M1 × M2])] =
    a match
      case i @ Id() =>
        val s = ~⚬.par(s1, s2)
        given KindN[M1 × M2] = s(a.outKind)
        Exists((s, Id()))
      case Lift(f) =>
        UnhandledCase.raise(s"PartialArgs.biShuffle($a, $s1, $s2)")
      case Par(f1, f2) =>
        UnhandledCase.raise(s"PartialArgs.biShuffle($a, $s1, $s2)")
      case Fst(f) =>
        UnhandledCase.raise(s"PartialArgs.biShuffle($a, $s1, $s2)")
      case Snd(f) =>
        UnhandledCase.raise(s"PartialArgs.biShuffle($a, $s1, $s2)")
      case IntroFst(f1, f2) =>
        (f1 shuffle s1, f2 shuffle s2) match
          case (Exists.Some((s1, f1)), Exists.Some((s2, f2))) =>
            s1.proveId(Kinds.unitIsNotPair) match
              case TypeEq(Refl()) =>
                Exists((s2, introFst(f1, f2)))
      case IntroSnd(f1, f2) =>
        (f1 shuffle s1, f2 shuffle s2) match
          case (Exists.Some((s1, f1)), Exists.Some((s2, f2))) =>
            s2.proveId(Kinds.unitIsNotPair) match
              case TypeEq(Refl()) =>
                Exists((s1, introSnd(f1, f2)))
      case IntroBoth(f1, f2) =>
        (f1 shuffle s1, f2 shuffle s2) match
          case (Exists.Some((s1, f1)), Exists.Some((s2, f2))) =>
            (s1.proveId(Kinds.unitIsNotPair), s2.proveId(Kinds.unitIsNotPair)) match
              case (TypeEq(Refl()), TypeEq(Refl())) =>
                Exists((~⚬.id, introBoth(f1, f2)))

  private def transfer[F[_, _], K, L1, L2, M1, M2](
    a: PartialArgs[F, K, L1 × L2],
    tr: Transfer[L1, L2, M1, M2],
  ): Exists[[X] =>> (K ~⚬ X, PartialArgs[F, X, M1 × M2])] =
    a match
      case Id() =>
        UnhandledCase.raise(s"PartialArgs.transfer($a, $tr)")
      case Lift(f) =>
        UnhandledCase.raise(s"PartialArgs.transfer($a, $tr)")
      case Par(f1, f2) =>
        UnhandledCase.raise(s"PartialArgs.transfer($a, $tr)")
      case Fst(f) =>
        UnhandledCase.raise(s"PartialArgs.transfer($a, $tr)")
      case Snd(f) =>
        UnhandledCase.raise(s"PartialArgs.transfer($a, $tr)")
      case IntroFst(f1, f2) =>
        tr match
          case Transfer.Swap() =>
            Exists(~⚬.id, introSnd(f2, f1))
          case lr: Transfer.AssocLR[l11, l12, l2, x2, x3] =>
            val (f11, f12) = unpair(f1.to[l11 × l12])
            introFst(f12, f2).shuffle(lr.g.asShuffle) match
              case Exists.Some((s, f2)) => Exists((s, introFst(f11, f2)))
          case rl: Transfer.AssocRL[l1, l21, l22, x1, x2] =>
            UnhandledCase.raise(s"PartialArgs.transfer($a, $tr)")
          case Transfer.IX(g) =>
            UnhandledCase.raise(s"PartialArgs.transfer($a, $tr)")
          case Transfer.XI(g) =>
            UnhandledCase.raise(s"PartialArgs.transfer($a, $tr)")
          case Transfer.IXI(g1, g2) =>
            UnhandledCase.raise(s"PartialArgs.transfer($a, $tr)")

      case IntroSnd(f1, f2) =>
        tr match
          case Transfer.Swap() =>
            Exists(~⚬.id, introFst(f2, f1))
          case lr: Transfer.AssocLR[l11, l12, l2, x2, x3] =>
            UnhandledCase.raise(s"PartialArgs.transfer($a, $tr)")
          case rl: Transfer.AssocRL[l1, l21, l22, x1, x2] =>
            val (f21, f22) = unpair(f2.to[l21 × l22])
            introSnd(f1, f21).shuffle(rl.g.asShuffle) match
              case Exists.Some((s, f1)) => Exists((s, introSnd(f1, f22)))
          case Transfer.IX(g) =>
            UnhandledCase.raise(s"PartialArgs.transfer($a, $tr)")
          case Transfer.XI(g) =>
            UnhandledCase.raise(s"PartialArgs.transfer($a, $tr)")
          case Transfer.IXI(g1, g2) =>
            UnhandledCase.raise(s"PartialArgs.transfer($a, $tr)")

      case IntroBoth(f1, f2) =>
        UnhandledCase.raise(s"PartialArgs.transfer($a, $tr)")

}
