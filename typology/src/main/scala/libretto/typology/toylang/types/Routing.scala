package libretto.typology.toylang.types

import libretto.lambda.{MappedMorphism, MonoidalObjectMap, Projection, Shuffle, SymmetricMonoidalCategory, UnhandledCase}
import libretto.lambda.util.{Exists, SourcePos, TypeEq}
import libretto.lambda.util.TypeEq.Refl
import libretto.typology.kinds._
import libretto.typology.types.kindShuffle
import libretto.typology.types.kindShuffle.~⚬

sealed trait Routing[K, L](using
  val inKind: Kinds[K],
  val outKind: Kinds[L],
) {
  import Routing.*

  def to[M](using lm: L =:= M): Routing[K, M] =
    lm.substituteCo[Routing[K, *]](this)

  def from[J](using jk: J =:= K): Routing[J, L] =
    jk.substituteContra[Routing[*, L]](this)

  def >[M](that: Routing[L, M]): Routing[K, M] =
    import that.outKind
    this match
      case Elim() =>
        proveId(that) match { case TypeEq(Refl()) => Elim() }
      case Impl(p, m, s) =>
        that match
          case Elim() =>
            Elim()
          case Impl(q, n, t) =>
            s.project(q) match
              case ~⚬.ProjectRes.Projected(q, s) =>
                m.project(q) match
                  case Exists.Some((q, m)) =>
                    n.preShuffle(s) match
                      case Exists.Some((n, s)) =>
                        Impl(p > q, m > n, s > t)

  def inFst[Y](using KindN[K], KindN[L], KindN[Y]): Routing[K × Y, L × Y] =
    Routing.fst(this)

  def inSnd[X](using KindN[X], KindN[K], KindN[L]): Routing[X × K, X × L] =
    Routing.snd(this)

  def applyTo[J](m: Multiplier[×, J, K])(using
    Kind[J],
    KindN[L],
  ): Multiplier[×, J, L]

  def applyTo[F[_, _], J](f: PartialArgs[F, J, K]): AppRes[F, J, L] =
    import f.inKind
    this match
      case Elim() =>
        UnhandledCase.raise(s"$this.applyTo($f)")
      case Impl(p, m, s) =>
        f.project(p) match
          case Exists.Some((p, f)) =>
            f.multiply(m) match
              case Exists.Some(Exists.Some((m, s1, f))) =>
                f.shuffle(s) match
                  case Exists.Some((s2, g)) =>
                    import g.inKind
                    AppRes(Routing(p, m, s1 > s2), g)

  private[types] def compile[==>[_, _], F[_, _], |*|[_, _], One, Q](fk: F[K, Q])(
    dupTypes: [k, q] => F[k, q] => (q ==> (q |*| q)),
  )(using
    F: MonoidalObjectMap[F, ×, ○, |*|, One],
    cat: SymmetricMonoidalCategory[==>, |*|, One],
  ): MappedMorphism[==>, F, K, L] =
    UnhandledCase.raise(s"$this.compile($fk)")
}

object Routing {
  case class Elim[K]()(using Kinds[K]) extends Routing[K, ○] {
    override def applyTo[J](m: Multiplier[×, J, K])(using
      j: Kind[J],
      o: KindN[○],
    ): Multiplier[×, J, ○] =
      KindN.cannotBeUnit(o)
  }

  case class Impl[K, P, Q, L](
    p: Projection[×, K, P],
    m: Multipliers.Proper[P, Q],
    s: Q ~⚬ L,
  )(using Kinds[K], Kinds[L]) extends Routing[K, L] {
    override def applyTo[J](n: Multiplier[×, J, K])(using
      j: Kind[J],
      l: KindN[L],
    ): Multiplier[×, J, L] =
      val n1 = (n project p)(j.isNotPair)
      s(m after n1)(using Multiplier.strongZippable(j.isNotPair))
  }

  def apply[K, P, Q, L](
    p: Projection[×, K, P],
    m: Multipliers[P, Q],
    s: Q ~⚬ L,
  )(using Kinds[K], Kinds[L]): Routing[K, L] =
    m match
      case m: Multipliers.Proper[p, q] =>
        Impl(p, m, s)
      case Multipliers.None =>
        summon[Kinds[L]].nonEmpty match
          case Left(TypeEq(Refl())) => Elim()
          case Right(l) =>
            val q: KindN[Q] = s.invert(l)
            KindN.cannotBeUnit(q)

  sealed trait AppRes[F[_, _], K, L]:
    type X
    def f: Routing[K, X]
    def g: PartialArgs[F, X, L]

  object AppRes {
    case class Impl[F[_, _], K, Y, L](
      f: Routing[K, Y],
      g: PartialArgs[F, Y, L],
    ) extends AppRes[F, K, L] {
      override type X = Y
    }

    def apply[F[_, _], K, Y, L](
      f: Routing[K, Y],
      g: PartialArgs[F, Y, L],
    ): AppRes[F, K, L] =
      Impl(f, g)
  }

  def id[K](using k: Kinds[K]): Routing[K, K] =
    k.nonEmpty match
      case Left(TypeEq(Refl())) => Elim()
      case Right(k) => Impl(Projection.id, Multipliers.idProper(using k), ~⚬.id)

  def par[K1: KindN, K2: KindN, L1: KindN, L2: KindN](
    f1: Routing[K1, L1],
    f2: Routing[K2, L2],
  ): Routing[K1 × K2, L1 × L2] =
    (f1, f2) match
      case (Impl(p1, m1, s1), Impl(p2, m2, s2)) =>
        Impl(Projection.par(p1, p2), Multipliers.Par(m1, m2), ~⚬.par(s1, s2))
      case (Elim(), _) =>
        KindN.cannotBeUnit(KindN[L1])
      case (_, Elim()) =>
        KindN.cannotBeUnit(KindN[L2])


  def fst[K: KindN, L: KindN, M: KindN](f: Routing[K, L]): Routing[K × M, L × M] =
    par(f, id)

  def snd[K: KindN, L: KindN, M: KindN](f: Routing[L, M]): Routing[K × L, K × M] =
    par(id, f)

  def assocLR[K: KindN, L: KindN, M: KindN]: Routing[(K × L) × M, K × (L × M)] =
    Impl(Projection.id, Multipliers.idProper, ~⚬.assocLR)

  def assocRL[K: KindN, L: KindN, M: KindN]: Routing[K × (L × M), (K × L) × M] =
    Impl(Projection.id, Multipliers.idProper, ~⚬.assocRL)

  def swap[K: KindN, L: KindN]: Routing[K × L, L × K] =
    Impl(Projection.id, Multipliers.idProper, ~⚬.swap)

  def elimFst[K: KindN, L: KindN]: Routing[K × L, L] =
    Impl(Projection.discardFst, Multipliers.idProper, ~⚬.id)

  def elimSnd[K: KindN, L: KindN]: Routing[K × L, K] =
    Impl(Projection.discardSnd, Multipliers.idProper, ~⚬.id)

  def dup[K](using k: KindN[K]): Routing[K, K × K] =
    dup0[K] match
      case Exists.Some((m, s)) =>
        Routing.Impl(Projection.Id(), m, s)

  private def dup0[K](using k: KindN[K]): Exists[[X] =>> (Multipliers.Proper[K, X], X ~⚬ (K × K))] =
    k match
      case KindN.Type =>
        summon[K =:= ●]
        Exists((Multipliers.dup[●], ~⚬.id))
      case KindN.Prod(k, l) =>
        (dup0(using k), dup0(using l)) match
          case (Exists.Some((m1, s1)), Exists.Some((m2, s2))) =>
            Exists((Multipliers.Par(m1, m2), ~⚬.par(s1, s2) > ~⚬.ixi))

  def ixi[K1: KindN, K2: KindN, K3: KindN, K4: KindN]: Routing[(K1 × K2) × (K3 × K4), (K1 × K3) × (K2 × K4)] =
    assocLR[K1, K2, K3 × K4] > snd(assocRL[K2, K3, K4] > fst(swap) > assocLR) > assocRL

  def elim[K](using k: Kinds[K]): Routing[K, ○] =
    Elim()

  def proveId[K](r: Routing[○, K]): K =:= ○ =
    r match
      case Elim() => summon[K =:= ○]
      case Impl(p, m, s) => UnhandledCase.raise(s"Routing.proveId($r)")

  def toMultiplier[K, L](r: Routing[K, L])(using
    k: Kind[K],
    l: KindN[L],
  ): Multiplier[×, K, L] =
    r.applyTo(Multiplier.Id())

  def untangle[K1, K2, L](r: Routing[K1 × K2, L]): UntangleRes[K1, K2, L] =
    import UntangleRes.*

    val (k1, k2) = Kinds.unpair(r.inKind)
    given Kinds[K1] = Kinds(k1)
    given Kinds[K2] = Kinds(k2)
    given Kinds[L] = r.outKind

    r match
      case Elim() =>
        UntangleRes.Eliminated()
      case Impl(p, m, s) =>
        p match
          case Projection.Id() =>
            untangle(Projection.Id(), Projection.Id(), m, s)
          case Projection.DiscardFst(p2) =>
            UnhandledCase.raise(s"Routing.untangle($r)")
          case Projection.DiscardSnd(p1) =>
            UnhandledCase.raise(s"Routing.untangle($r)")
          case Projection.Fst(p1) =>
            UnhandledCase.raise(s"Routing.untangle($r)")
          case Projection.Snd(p2) =>
            UnhandledCase.raise(s"Routing.untangle($r)")
          case Projection.Both(p1, p2) =>
            UnhandledCase.raise(s"Routing.untangle($r)")

  private def untangle[K1, K2, P1, P2, Q, L](
    p1: Projection[×, K1, P1],
    p2: Projection[×, K2, P2],
    m: Multipliers[P1 × P2, Q],
    s: Q ~⚬ L,
  )(using
    Kinds[K1],
    Kinds[K2],
    Kinds[L],
  ): UntangleRes[K1, K2, L] =
    m match
      case Multipliers.Par(m1, m2) =>
        untangle(p1, p2, m1, m2, s)
      case s @ Multipliers.Single(_) =>
        Kind.cannotBePair(s.inKind)

  private def untangle[K1, K2, P1, P2, Q1, Q2, L](
    p1: Projection[×, K1, P1],
    p2: Projection[×, K2, P2],
    m1: Multipliers.Proper[P1, Q1],
    m2: Multipliers.Proper[P2, Q2],
    s: (Q1 × Q2) ~⚬ L,
  )(using
    Kinds[K1],
    Kinds[K2],
    Kinds[L],
  ): UntangleRes[K1, K2, L] =
    ~⚬.decompose1(s) match
      case ~⚬.Decomposition1(s1, s2, tr, ev @ TypeEq(Refl())) =>
        val (r1, r2) =
          KindN.unpair(
            tr.asShuffle.invert.apply(Kinds.nonEmpty(ev.substituteContra(summon[Kinds[L]])))
          )
        UntangleRes.Decomposed(
          Impl(p1, m1, s1)(using summon, Kinds(r1)),
          Impl(p2, m2, s2)(using summon, Kinds(r2)),
          tr,
        )

  sealed trait UntangleRes[K1, K2, L]
  object UntangleRes {
    case class Eliminated[K1, K2]() extends UntangleRes[K1, K2, ○]
    case class FstEliminated[K1, K2, L](f2: Routing[K2, L]) extends UntangleRes[K1, K2, L]
    case class SndEliminated[K1, K2, L](f1: Routing[K1, L]) extends UntangleRes[K1, K2, L]
    case class Decomposed[K1, K2, Q1, Q2, L1, L2](
      f1: Routing[K1, Q1],
      f2: Routing[K2, Q2],
      tr: kindShuffle.TransferOpt[Q1, Q2, L1, L2],
    ) extends UntangleRes[K1, K2, L1 × L2]
  }

  def traceSnd[K1, K2, L](r: Routing[K1 × K2, L])(using
    k2: Kind[K2],
    l: KindN[L],
  ): TraceSndRes[K1, K2, L] =
    import TraceSndRes.{FstEliminated, SndEliminated, Traced}
    untangle(r) match
      case UntangleRes.Eliminated() => KindN.cannotBeUnit(l)
      case UntangleRes.FstEliminated(r2) => FstEliminated(toMultiplier(r2))
      case UntangleRes.SndEliminated(r1) => SndEliminated(r1)
      case UntangleRes.Decomposed(r1, r2, tr) =>
        val (q1, q2) = KindN.unpair(tr.asShuffle.invert.apply(l))
        Traced(r1, toMultiplier(r2)(using k2, q2), tr)

  sealed trait TraceSndRes[K1, K2, L]
  object TraceSndRes {
    case class FstEliminated[K1, K2, L](m: Multiplier[×, K2, L]) extends TraceSndRes[K1, K2, L]
    case class SndEliminated[K1, K2, L](r: Routing[K1, L]) extends TraceSndRes[K1, K2, L]

    case class Traced[K1, K2, Q1, Q2, L1, L2](
      r: Routing[K1, Q1],
      m: Multiplier[×, K2, Q2],
      tr: kindShuffle.TransferOpt[Q1, Q2, L1, L2],
    ) extends TraceSndRes[K1, K2, L1 × L2]
  }
}
