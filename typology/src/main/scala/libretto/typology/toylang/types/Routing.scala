package libretto.typology.toylang.types

import libretto.lambda.{MappedMorphism, MonoidalObjectMap, Projection, Shuffle, SymmetricMonoidalCategory, UnhandledCase}
import libretto.lambda.util.{Exists, SourcePos, TypeEq}
import libretto.lambda.util.TypeEq.Refl
import libretto.typology.kinds._
import libretto.typology.types.kindShuffle
import libretto.typology.types.kindShuffle.~⚬

sealed trait Routing[K, L](using
  val inKind: Kind[K],
  val outKind: Kind[L],
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

  def inFst[Y](using ProperKind[K], ProperKind[L], ProperKind[Y]): Routing[K × Y, L × Y] =
    Routing.fst(this)

  def inSnd[X](using ProperKind[X], ProperKind[K], ProperKind[L]): Routing[X × K, X × L] =
    Routing.snd(this)

  def applyTo[J](m: Multiplier[×, J, K])(using
    OutputKind[J],
    ProperKind[L],
  ): Multiplier[×, J, L]

  def applyTo[F[_, _], J](f: PartialArgs[F, J, K]): AppRes[F, J, L] = {
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

    // this match {
    //   case Id() =>
    //     AppRes(Id(), f)
    //   case AndThen(p, q) =>
    //     p.applyTo(f) match {
    //       case AppRes.Impl(p, f) =>
    //         q.applyTo(f) match {
    //           case AppRes.Impl(q, f) =>
    //             AppRes(p > q, f)
    //         }
    //     }
    //   case p: Par[k1, k2, l1, l2] =>
    //     given ProperKind[k1] = Kind.fst(p.inKind)
    //     given ProperKind[k2] = Kind.snd(p.inKind)
    //     given ProperKind[l1] = Kind.fst(p.outKind)
    //     given ProperKind[l2] = Kind.snd(p.outKind)

    //     def go[K1: ProperKind, K2: ProperKind, L1: ProperKind, L2: ProperKind](
    //       f: PartialArgs[F, J, K1 × K2],
    //       g1: Routing[K1, L1],
    //       g2: Routing[K2, L2],
    //     ): AppRes[F, J, L1 × L2] =
    //       f match {
    //         case PartialArgs.IntroFst(f1, f2) =>
    //           val h1 = g1.applyTo0(f1)
    //           g2.applyTo(f2) match
    //             case AppRes.Impl(r, h2) =>
    //               AppRes(r, PartialArgs.introFst(h1, h2))
    //         case PartialArgs.IntroBoth(f1, f2) =>
    //           AppRes(id, PartialArgs.introBoth(g1.applyTo0(f1), g2.applyTo0(f2)))
    //         case f: PartialArgs.Fst[f, j1, k1, k2] =>
    //           import f.inKind1
    //           val r = g1.applyTo(f.f)
    //           r.g.inKind.properKind match
    //             case Left(ev) =>
    //               AppRes(elimFst[j1, K2] > g2, PartialArgs.introFst(r.g.from[○](using ev.flip)))
    //             case Right(x) =>
    //               given ProperKind[r.X] = x
    //               AppRes(Par(r.f, g2), PartialArgs.fst(r.g))
    //         case f: PartialArgs.Par[f, j1, j2, k1, k2] =>
    //           import f.given
    //           val r1 = g1.applyTo(f.f1)
    //           val r2 = g2.applyTo(f.f2)
    //           r1.f.outKind.properKind match
    //             case Left(ev1) =>
    //               AppRes(elimFst[j1, j2] > r2.f, PartialArgs.introFst(r1.g.from[○](using ev1.flip), r2.g))
    //             case Right(x) =>
    //               given ProperKind[r1.X] = x
    //               r2.f.outKind.properKind match
    //                 case Left(ev2) =>
    //                   AppRes(elimSnd[j1, j2] > r1.f, PartialArgs.introSnd(r1.g, r2.g.from[○](using ev2.flip)))
    //                 case Right(y) =>
    //                   given ProperKind[r2.X] = y
    //                   AppRes(par(r1.f, r2.f), PartialArgs.par(r1.g, r2.g))
    //         case other =>
    //           throw new NotImplementedError(s"$other (${summon[SourcePos]})")
    //       }

    //     go[k1, k2, l1, l2](f, p.f1, p.f2)
    //   case Dup() =>
    //     f.inKind.properKind match {
    //       case Left(j_eq_○) =>
    //         val f0: PartialArgs[F, ○, K] = j_eq_○.substituteCo[PartialArgs[F, *, K]](f)
    //         AppRes(id[J].to[○](using j_eq_○), PartialArgs.introBoth(f0, f0))
    //       case Right(j) =>
    //         given ProperKind[J] = j
    //         AppRes(dup[J], PartialArgs.par(f, f))
    //     }
    //   case ElimFst() =>
    //     f match {
    //       case PartialArgs.IntroBoth(f1, f2) =>
    //         AppRes(id, f2)
    //       case other =>
    //         throw new NotImplementedError(s"$other (${summon[SourcePos]})")
    //     }
    //   case ElimSnd() =>
    //     f match {
    //       case PartialArgs.IntroFst(f1, f2) =>
    //         AppRes(elim, f1)
    //       case other =>
    //         UnhandledCase.raise(s"Applying $this to $f")
    //     }
    //   case a: AssocLR[k, l, m] =>
    //     f match {
    //       case f @ PartialArgs.IntroFst(f1, f2) =>
    //         import f.given
    //         f1 match
    //           case PartialArgs.IntroBoth(f11, f12) =>
    //             AppRes(id, PartialArgs.IntroFst(f11, PartialArgs.IntroFst(f12, f2)))
    //           case other =>
    //             UnhandledCase.raise(s"Applying $this to $f")
    //       case f @ PartialArgs.Fst(f1) =>
    //         import f.kind2
    //         f1 match
    //           case f1 @ PartialArgs.IntroSnd(f11, f12) =>
    //             import f1.inKindProper
    //             AppRes(id, PartialArgs.par(f11, PartialArgs.introFst[F, l, m](f12)))
    //           case other =>
    //             UnhandledCase.raise(s"Applying $this to $f")
    //       case other =>
    //         UnhandledCase.raise(s"Applying $this to $f")
    //     }
    //   case a: AssocRL[k, l, m] =>
    //     import a.given
    //     f match {
    //       case PartialArgs.IntroFst(f1, f2) =>
    //         f2 match
    //           case PartialArgs.Id() =>
    //             AppRes(id, PartialArgs.Fst[F, l, k × l, m](PartialArgs.IntroFst(f1, PartialArgs.Id[F, l]())))
    //           case f2 @ PartialArgs.Snd(f22) =>
    //             import f2.inKind2
    //             AppRes(id, PartialArgs.Par(PartialArgs.IntroFst(f1, PartialArgs.Id[F, l]()), f22))
    //           case other =>
    //             UnhandledCase.raise(s"Applying $this to $f")
    //       case other =>
    //         UnhandledCase.raise(s"Applying $this to $f")
    //     }
    //   case Swap() =>
    //     f match {
    //       case f @ PartialArgs.IntroFst(f1, f2) =>
    //         import f.given
    //         AppRes(id, PartialArgs.IntroSnd(f2, f1))
    //       case other =>
    //         UnhandledCase.raise(s"Applying $this to $f")
    //     }
    //   case other =>
    //     UnhandledCase.raise(s"Applying $other to $f")
    // }
  }

  private def applyTo0[F[_, _]](f: PartialArgs[F, ○, K]): PartialArgs[F, ○, L] =
    applyTo(f) match {
      case AppRes.Impl(r, f) =>
        proveId(r).substituteCo[PartialArgs[F, _, L]](f)
    }

  def compile[==>[_, _], F[_, _], |*|[_, _], One, Q](fk: F[K, Q])(
    dupTypes: [k, q] => F[k, q] => (q ==> (q |*| q)),
  )(using
    F: MonoidalObjectMap[F, ×, ○, |*|, One],
    cat: SymmetricMonoidalCategory[==>, |*|, One],
  ): MappedMorphism[==>, F, K, L] = {
    UnhandledCase.raise(s"$this.compile($fk)")
    // this match
    //   case Id() =>
    //     MappedMorphism(fk, cat.id, fk)
    //   case _: AssocLR[k, l, m] =>
    //     val fk_ = F.unpair[(k × l), m, Q](fk)
    //     val fk12 = F.unpair(fk_.f1)
    //     val fk1 = fk12.f1
    //     val fk2 = fk12.f2
    //     val fk3 = fk_.f2
    //     MappedMorphism(
    //       F.pair(F.pair(fk1, fk2), fk3),
    //       cat.assocLR,
    //       F.pair(fk1, F.pair(fk2, fk3)),
    //     )
    //   case _: AssocRL[k, l, m] =>
    //     val fk_ = F.unpair[k, l × m, Q](fk)
    //     val fk23 = F.unpair(fk_.f2)
    //     val fk1 = fk_.f1
    //     val fk2 = fk23.f1
    //     val fk3 = fk23.f2
    //     MappedMorphism(
    //       F.pair(fk1, F.pair(fk2, fk3)),
    //       cat.assocRL,
    //       F.pair(F.pair(fk1, fk2), fk3),
    //     )
    //   case _: Swap[k, l] =>
    //     val fk_ = F.unpair[k, l, Q](fk)
    //     val fk1 = fk_.f1
    //     val fk2 = fk_.f2
    //     MappedMorphism(
    //       F.pair(fk1, fk2),
    //       cat.swap,
    //       F.pair(fk2, fk1),
    //     )
    //   case ElimFst() =>
    //     throw NotImplementedError(s"at ${summon[SourcePos]}")
    //   case ElimSnd() =>
    //     throw NotImplementedError(s"at ${summon[SourcePos]}")
    //   case AndThen(f, g) =>
    //     val f1 = f.compile[==>, F, |*|, One, Q](fk)(dupTypes)
    //     val g1 = g.compile[==>, F, |*|, One, f1.FB](f1.tgtMap)(dupTypes)
    //     f1 > g1
    //   case Par(f1, f2) =>
    //     throw NotImplementedError(s"at ${summon[SourcePos]}")
    //   case Elim() =>
    //     throw NotImplementedError(s"at ${summon[SourcePos]}")
    //   case Dup() =>
    //     MappedMorphism(fk, dupTypes(fk), F.pair(fk, fk))
  }
}

object Routing {
  case class Elim[K]()(using Kind[K]) extends Routing[K, ○] {
    override def applyTo[J](m: Multiplier[×, J, K])(using
      j: OutputKind[J],
      o: ProperKind[○],
    ): Multiplier[×, J, ○] =
      ProperKind.cannotBeUnit(o)
  }

  case class Impl[K, P, Q, L](
    p: Projection[×, K, P],
    m: Multipliers.Proper[P, Q],
    s: Q ~⚬ L,
  )(using Kind[K], Kind[L]) extends Routing[K, L] {
    override def applyTo[J](n: Multiplier[×, J, K])(using
      j: OutputKind[J],
      l: ProperKind[L],
    ): Multiplier[×, J, L] =
      val n1 = (n project p)(j.isNotPair)
      s(m after n1)(using Multiplier.strongZippable(j.isNotPair))
  }

  def apply[K, P, Q, L](
    p: Projection[×, K, P],
    m: Multipliers[P, Q],
    s: Q ~⚬ L,
  )(using Kind[K], Kind[L]): Routing[K, L] =
    m match
      case m: Multipliers.Proper[p, q] =>
        Impl(p, m, s)
      case Multipliers.None =>
        summon[Kind[L]].properKind match
          case Left(TypeEq(Refl())) => Elim()
          case Right(l) =>
            val q: ProperKind[Q] = s.invert(l)
            ProperKind.cannotBeUnit(q)

  // case class AndThen[K, L, M](
  //   f: Routing[K, L],
  //   g: Routing[L, M],
  // ) extends Routing[K, M](using f.inKind, g.outKind) {
  //   override def applyTo[J](m: Multiplier[×, J, K])(using
  //     J: OutputKind[J],
  //     M: ProperKind[M],
  //   ): Multiplier[×, J, M] =
  //     g.inKind.properKind match
  //       case Left(TypeEq(Refl())) =>
  //         proveId[M](g) match { case TypeEq(Refl()) =>
  //           ProperKind.cannotBeUnit(M)
  //         }
  //       case Right(l) =>
  //         given ProperKind[L] = l
  //         g.applyTo(f.applyTo(m))
  // }

  // case class Id[K: Kind]() extends Routing[K, K] {
  //   override def applyTo[J](m: Multiplier[×, J, K])(using
  //     OutputKind[J],
  //     ProperKind[K],
  //   ): Multiplier[×, J, K] =
  //     m
  // }

  // case class Par[K1: ProperKind, K2: ProperKind, L1: ProperKind, L2: ProperKind](
  //   f1: Routing[K1, L1],
  //   f2: Routing[K2, L2],
  // ) extends Routing[K1 × K2, L1 × L2] {
  //   override def applyTo[J](m: Multiplier[×, J, K1 × K2])(using
  //     J: OutputKind[J],
  //     L: ProperKind[L1 × L2],
  //   ): Multiplier[×, J, L1 × L2] =
  //     m match
  //       case Multiplier.Id() =>
  //         summon[J =:= (K1 × K2)]
  //         OutputKind.cannotBePair(J: OutputKind[K1 × K2])
  //       case Multiplier.Dup(m1, m2) =>
  //         Multiplier.Dup(f1.applyTo(m1), f2.applyTo(m2))
  // }

  // case class AssocLR[K: ProperKind, L: ProperKind, M: ProperKind]() extends Routing[(K × L) × M, K × (L × M)] {
  //   override def applyTo[J](m: Multiplier[×, J, (K × L) × M])(using
  //     j: OutputKind[J],
  //     klm: ProperKind[K × (L × M)],
  //   ): Multiplier[×, J, K × (L × M)] =
  //     m match
  //       case Multiplier.Id() =>
  //         summon[J =:= ((K × L) × M)]
  //         OutputKind.cannotBePair(j: OutputKind[(K × L) × M])
  //       case Multiplier.Dup(m1, m2) =>
  //         m1 match
  //           case Multiplier.Id() =>
  //             summon[J =:= (K × L)]
  //             OutputKind.cannotBePair(j: OutputKind[K × L])
  //           case Multiplier.Dup(m11, m12) =>
  //             Multiplier.Dup(m11, Multiplier.Dup(m12, m2))
  // }

  // case class AssocRL[K, L, M]()(using
  //   val K: ProperKind[K],
  //   val L: ProperKind[L],
  //   val M: ProperKind[M],
  // ) extends Routing[K × (L × M), (K × L) × M] {
  //   override def applyTo[J](m: Multiplier[×, J, K × (L × M)])(using
  //     OutputKind[J],
  //     ProperKind[(K × L) × M],
  //   ): Multiplier[×, J, (K × L) × M] =
  //     UnhandledCase.raise(s"$this.applyTo($m)")
  // }

  // case class Swap[K: ProperKind, L: ProperKind]() extends Routing[K × L, L × K] {
  //   override def applyTo[J](m: Multiplier[[K, L] =>> K × L, J, K × L])(using OutputKind[J], ProperKind[L × K]): Multiplier[[K, L] =>> K × L, J, L × K] =
  //     UnhandledCase.raise(s"$this.applyTo($m)")
  // }

  // case class Elim[K: ProperKind]() extends Routing[K, ○] {
  //   override def applyTo[J](m: Multiplier[[K, L] =>> K × L, J, K])(using OutputKind[J], ProperKind[○]): Multiplier[[K, L] =>> K × L, J, ○] =
  //     UnhandledCase.raise(s"$this.applyTo($m)")
  // }

  // case class ElimFst[K: ProperKind, L: ProperKind]() extends Routing[K × L, L] {
  //   override def applyTo[J](m: Multiplier[[K, L] =>> K × L, J, K × L])(using OutputKind[J], ProperKind[L]): Multiplier[[K, L] =>> K × L, J, L] =
  //     UnhandledCase.raise(s"$this.applyTo($m)")
  // }

  // case class ElimSnd[K: ProperKind, L: ProperKind]() extends Routing[K × L, K] {
  //   override def applyTo[J](m: Multiplier[[K, L] =>> K × L, J, K × L])(using OutputKind[J], ProperKind[K]): Multiplier[[K, L] =>> K × L, J, K] =
  //     UnhandledCase.raise(s"$this.applyTo($m)")
  // }

  // case class Dup[K]()(using val kind: OutputKind[K]) extends Routing[K, K × K] {
  //   override def applyTo[J](m: Multiplier[[K, L] =>> K × L, J, K])(using OutputKind[J], ProperKind[K × K]): Multiplier[[K, L] =>> K × L, J, K × K] =
  //     UnhandledCase.raise(s"$this.applyTo($m)")
  // }

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

  def id[K](using k: Kind[K]): Routing[K, K] =
    k.properKind match
      case Left(TypeEq(Refl())) => Elim()
      case Right(k) => Impl(Projection.id, Multipliers.idProper(using k), ~⚬.id)

  def par[K1: ProperKind, K2: ProperKind, L1: ProperKind, L2: ProperKind](
    f1: Routing[K1, L1],
    f2: Routing[K2, L2],
  ): Routing[K1 × K2, L1 × L2] =
    UnhandledCase.raise(s"Routing.par($f1, $f2)")

  def fst[K: ProperKind, L: ProperKind, M: ProperKind](f: Routing[K, L]): Routing[K × M, L × M] =
    par(f, id)

  def snd[K: ProperKind, L: ProperKind, M: ProperKind](f: Routing[L, M]): Routing[K × L, K × M] =
    par(id, f)

  def assocLR[K: ProperKind, L: ProperKind, M: ProperKind]: Routing[(K × L) × M, K × (L × M)] =
    UnhandledCase.raise(s"Routing.assocLR")

  def assocRL[K: ProperKind, L: ProperKind, M: ProperKind]: Routing[K × (L × M), (K × L) × M] =
    UnhandledCase.raise(s"Routing.assocRL")

  def swap[K: ProperKind, L: ProperKind]: Routing[K × L, L × K] =
    UnhandledCase.raise(s"Routing.swap")

  def elimFst[K: ProperKind, L: ProperKind]: Routing[K × L, L] =
    UnhandledCase.raise(s"Routing.elimFst")

  def elimSnd[K: ProperKind, L: ProperKind]: Routing[K × L, K] =
    UnhandledCase.raise(s"Routing.elimSnd")

  def dup[K: ProperKind]: Routing[K, K × K] =
    UnhandledCase.raise(s"Routing.dup")
    // ProperKind[K] match {
    //   case ProperKind.Type =>
    //     Dup()(using OutputKind[●])
    //   case ProperKind.Prod(k1, k2) =>
    //     def go[K1, K2](using k1: ProperKind[K1], k2: ProperKind[K2]): Routing[K1 × K2, (K1 × K2) × (K1 × K2)] =
    //       par(dup[K1], dup[K2]) > ixi
    //     go(using k1, k2)
    // }

  def ixi[K1: ProperKind, K2: ProperKind, K3: ProperKind, K4: ProperKind]: Routing[(K1 × K2) × (K3 × K4), (K1 × K3) × (K2 × K4)] =
    assocLR[K1, K2, K3 × K4] > snd(assocRL[K2, K3, K4] > fst(swap) > assocLR) > assocRL

  def elim[K](using k: Kind[K]): Routing[K, ○] =
    Elim()
    // k.properKind match {
    //   case Left(k_eq_○) => id[K].to(using k_eq_○)
    //   case Right(k)     => Elim[K]()(using k)
    // }

  def proveId[K](r: Routing[○, K]): K =:= ○ =
    r match
      case Elim() => summon[K =:= ○]
      case Impl(p, m, s) => UnhandledCase.raise(s"Routing.proveId($r)")
    // r match {
    //   case Id() =>
    //     implicitly[K =:= ○]
    //   case AndThen(p, q) =>
    //     proveId(proveId(p).substituteCo[Routing[*, K]](q))
    //   case other =>
    //     throw new NotImplementedError(s"$other (${summon[SourcePos]})")
    // }

  def toMultiplier[K, L](r: Routing[K, L])(using
    k: OutputKind[K],
    l: ProperKind[L],
  ): Multiplier[×, K, L] =
    r.applyTo(Multiplier.Id())

  def untangle[K1, K2, L](r: Routing[K1 × K2, L]): UntangleRes[K1, K2, L] =
    import UntangleRes.*

    val (k1, k2) = ProperKind.unpair(r.inKind)
    given Kind[K1] = k1.kind
    given Kind[K2] = k2.kind
    given Kind[L] = r.outKind

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
    Kind[K1],
    Kind[K2],
    Kind[L],
  ): UntangleRes[K1, K2, L] =
    m match
      case Multipliers.Par(m1, m2) =>
        untangle(p1, p2, m1, m2, s)
      case s @ Multipliers.Single(_) =>
        OutputKind.cannotBePair(s.inKind)

  private def untangle[K1, K2, P1, P2, Q1, Q2, L](
    p1: Projection[×, K1, P1],
    p2: Projection[×, K2, P2],
    m1: Multipliers.Proper[P1, Q1],
    m2: Multipliers.Proper[P2, Q2],
    s: (Q1 × Q2) ~⚬ L,
  )(using
    Kind[K1],
    Kind[K2],
    Kind[L],
  ): UntangleRes[K1, K2, L] =
    ~⚬.decompose1(s) match
      case ~⚬.Decomposition1(s1, s2, tr, ev @ TypeEq(Refl())) =>
        val (r1, r2) =
          ProperKind.unpair(
            tr.asShuffle.invert.apply(ProperKind.fromProd(ev.substituteContra(summon[Kind[L]])))
          )
        UntangleRes.Decomposed(
          Impl(p1, m1, s1)(using summon, r1.kind),
          Impl(p2, m2, s2)(using summon, r2.kind),
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
    k2: OutputKind[K2],
    l: ProperKind[L],
  ): TraceSndRes[K1, K2, L] =
    import TraceSndRes.{FstEliminated, SndEliminated, Traced}
    untangle(r) match
      case UntangleRes.Eliminated() => ProperKind.cannotBeUnit(l)
      case UntangleRes.FstEliminated(r2) => FstEliminated(toMultiplier(r2))
      case UntangleRes.SndEliminated(r1) => SndEliminated(r1)
      case UntangleRes.Decomposed(r1, r2, tr) =>
        val (q1, q2) = ProperKind.unpair(tr.asShuffle.invert.apply(l))
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
