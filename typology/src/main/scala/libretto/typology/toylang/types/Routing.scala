package libretto.typology.toylang.types

import libretto.lambda.{MappedMorphism, MonoidalObjectMap, SymmetricMonoidalCategory, UnhandledCase}
import libretto.lambda.util.{SourcePos, TypeEq}
import libretto.lambda.util.TypeEq.Refl
import libretto.typology.kinds._

sealed trait Routing[K, L](using
  val inKind: Kind[K],
  val outKind: Kind[L],
) {
  import Routing._

  def to[M](using lm: L =:= M): Routing[K, M] =
    lm.substituteCo[Routing[K, *]](this)

  def from[J](using jk: J =:= K): Routing[J, L] =
    jk.substituteContra[Routing[*, L]](this)

  def >[M](that: Routing[L, M]): Routing[K, M] =
    AndThen(this, that)

  def inFst[Y](using ProperKind[K], ProperKind[L], ProperKind[Y]): Routing[K × Y, L × Y] =
    Routing.fst(this)

  def inSnd[X](using ProperKind[X], ProperKind[K], ProperKind[L]): Routing[X × K, X × L] =
    Routing.snd(this)

  def applyTo[F[_, _], J](f: PartialArgs[F, J, K]): AppTransRes[F, J, L] = {
    import f.inKind

    this match {
      case Id() =>
        AppTransRes(Id(), f)
      case AndThen(p, q) =>
        p.applyTo(f) match {
          case AppTransRes.Impl(p, f) =>
            q.applyTo(f) match {
              case AppTransRes.Impl(q, f) =>
                AppTransRes(p > q, f)
            }
        }
      case p: Par[k1, k2, l1, l2] =>
        given ProperKind[k1] = Kind.fst(p.inKind)
        given ProperKind[k2] = Kind.snd(p.inKind)
        given ProperKind[l1] = Kind.fst(p.outKind)
        given ProperKind[l2] = Kind.snd(p.outKind)

        def go[K1: ProperKind, K2: ProperKind, L1: ProperKind, L2: ProperKind](
          f: PartialArgs[F, J, K1 × K2],
          g1: Routing[K1, L1],
          g2: Routing[K2, L2],
        ): AppTransRes[F, J, L1 × L2] =
          f match {
            case PartialArgs.IntroFst(f1, f2) =>
              val h1 = g1.applyTo0(f1)
              g2.applyTo(f2) match
                case AppTransRes.Impl(r, h2) =>
                  AppTransRes(r, PartialArgs.introFst(h1, h2))
            case PartialArgs.IntroBoth(f1, f2) =>
              AppTransRes(id, PartialArgs.introBoth(g1.applyTo0(f1), g2.applyTo0(f2)))
            case f: PartialArgs.Fst[f, j1, k1, k2] =>
              import f.inKind1
              val r = g1.applyTo(f.f)
              r.g.inKind.properKind match
                case Left(ev) =>
                  AppTransRes(elimFst[j1, K2] > g2, PartialArgs.introFst(r.g.from[○](using ev.flip)))
                case Right(x) =>
                  given ProperKind[r.X] = x
                  AppTransRes(Par(r.f, g2), PartialArgs.fst(r.g))
            case f: PartialArgs.Par[f, j1, j2, k1, k2] =>
              import f.given
              val r1 = g1.applyTo(f.f1)
              val r2 = g2.applyTo(f.f2)
              r1.f.outKind.properKind match
                case Left(ev1) =>
                  AppTransRes(elimFst[j1, j2] > r2.f, PartialArgs.introFst(r1.g.from[○](using ev1.flip), r2.g))
                case Right(x) =>
                  given ProperKind[r1.X] = x
                  r2.f.outKind.properKind match
                    case Left(ev2) =>
                      AppTransRes(elimSnd[j1, j2] > r1.f, PartialArgs.introSnd(r1.g, r2.g.from[○](using ev2.flip)))
                    case Right(y) =>
                      given ProperKind[r2.X] = y
                      AppTransRes(par(r1.f, r2.f), PartialArgs.par(r1.g, r2.g))
            case other =>
              throw new NotImplementedError(s"$other (${summon[SourcePos]})")
          }

        go[k1, k2, l1, l2](f, p.f1, p.f2)
      case Dup() =>
        f.inKind.properKind match {
          case Left(j_eq_○) =>
            val f0: PartialArgs[F, ○, K] = j_eq_○.substituteCo[PartialArgs[F, *, K]](f)
            AppTransRes(id[J].to[○](using j_eq_○), PartialArgs.introBoth(f0, f0))
          case Right(j) =>
            given ProperKind[J] = j
            AppTransRes(dup[J], PartialArgs.par(f, f))
        }
      case ElimFst() =>
        f match {
          case PartialArgs.IntroBoth(f1, f2) =>
            AppTransRes(id, f2)
          case other =>
            throw new NotImplementedError(s"$other (${summon[SourcePos]})")
        }
      case ElimSnd() =>
        f match {
          case PartialArgs.IntroFst(f1, f2) =>
            AppTransRes(elim, f1)
          case other =>
            UnhandledCase.raise(s"Applying $this to $f")
        }
      case a: AssocLR[k, l, m] =>
        f match {
          case f @ PartialArgs.IntroFst(f1, f2) =>
            import f.given
            f1 match
              case PartialArgs.IntroBoth(f11, f12) =>
                AppTransRes(id, PartialArgs.IntroFst(f11, PartialArgs.IntroFst(f12, f2)))
              case other =>
                UnhandledCase.raise(s"Applying $this to $f")
          case f @ PartialArgs.Fst(f1) =>
            import f.kind2
            f1 match
              case f1 @ PartialArgs.IntroSnd(f11, f12) =>
                import f1.inKindProper
                AppTransRes(id, PartialArgs.par(f11, PartialArgs.introFst[F, l, m](f12)))
              case other =>
                UnhandledCase.raise(s"Applying $this to $f")
          case other =>
            UnhandledCase.raise(s"Applying $this to $f")
        }
      case a: AssocRL[k, l, m] =>
        import a.given
        f match {
          case PartialArgs.IntroFst(f1, f2) =>
            f2 match
              case PartialArgs.Id() =>
                AppTransRes(id, PartialArgs.Fst[F, l, k × l, m](PartialArgs.IntroFst(f1, PartialArgs.Id[F, l]())))
              case f2 @ PartialArgs.Snd(f22) =>
                import f2.inKind2
                AppTransRes(id, PartialArgs.Par(PartialArgs.IntroFst(f1, PartialArgs.Id[F, l]()), f22))
              case other =>
                UnhandledCase.raise(s"Applying $this to $f")
          case other =>
            UnhandledCase.raise(s"Applying $this to $f")
        }
      case Swap() =>
        f match {
          case f @ PartialArgs.IntroFst(f1, f2) =>
            import f.given
            AppTransRes(id, PartialArgs.IntroSnd(f2, f1))
          case other =>
            UnhandledCase.raise(s"Applying $this to $f")
        }
      case other =>
        UnhandledCase.raise(s"Applying $other to $f")
    }
  }

  private def applyTo0[F[_, _]](f: PartialArgs[F, ○, K]): PartialArgs[F, ○, L] =
    applyTo(f) match {
      case AppTransRes.Impl(r, f) =>
        proveId(r).substituteCo[PartialArgs[F, *, L]](f)
    }

  def compile[==>[_, _], F[_, _], |*|[_, _], One, Q](fk: F[K, Q])(
    dupTypes: [k, q] => F[k, q] => (q ==> (q |*| q)),
  )(using
    F: MonoidalObjectMap[F, ×, ○, |*|, One],
    cat: SymmetricMonoidalCategory[==>, |*|, One],
  ): MappedMorphism[==>, F, K, L] = {
    this match
      case Id() =>
        MappedMorphism(fk, cat.id, fk)
      case _: AssocLR[k, l, m] =>
        val fk_ = F.unpair[(k × l), m, Q](fk)
        val fk12 = F.unpair(fk_.f1)
        val fk1 = fk12.f1
        val fk2 = fk12.f2
        val fk3 = fk_.f2
        MappedMorphism(
          F.pair(F.pair(fk1, fk2), fk3),
          cat.assocLR,
          F.pair(fk1, F.pair(fk2, fk3)),
        )
      case _: AssocRL[k, l, m] =>
        val fk_ = F.unpair[k, l × m, Q](fk)
        val fk23 = F.unpair(fk_.f2)
        val fk1 = fk_.f1
        val fk2 = fk23.f1
        val fk3 = fk23.f2
        MappedMorphism(
          F.pair(fk1, F.pair(fk2, fk3)),
          cat.assocRL,
          F.pair(F.pair(fk1, fk2), fk3),
        )
      case _: Swap[k, l] =>
        val fk_ = F.unpair[k, l, Q](fk)
        val fk1 = fk_.f1
        val fk2 = fk_.f2
        MappedMorphism(
          F.pair(fk1, fk2),
          cat.swap,
          F.pair(fk2, fk1),
        )
      case ElimFst() =>
        throw NotImplementedError(s"at ${summon[SourcePos]}")
      case ElimSnd() =>
        throw NotImplementedError(s"at ${summon[SourcePos]}")
      case AndThen(f, g) =>
        val f1 = f.compile[==>, F, |*|, One, Q](fk)(dupTypes)
        val g1 = g.compile[==>, F, |*|, One, f1.FB](f1.tgtMap)(dupTypes)
        f1 > g1
      case Par(f1, f2) =>
        throw NotImplementedError(s"at ${summon[SourcePos]}")
      case Elim() =>
        throw NotImplementedError(s"at ${summon[SourcePos]}")
      case Dup() =>
        MappedMorphism(fk, dupTypes(fk), F.pair(fk, fk))
  }
}

object Routing {
  case class AndThen[K, L, M](
    f: Routing[K, L],
    g: Routing[L, M],
  ) extends Routing[K, M](using f.inKind, g.outKind)

  case class Id[K: Kind]() extends Routing[K, K]

  case class Par[K1: ProperKind, K2: ProperKind, L1: ProperKind, L2: ProperKind](
    f1: Routing[K1, L1],
    f2: Routing[K2, L2],
  ) extends Routing[K1 × K2, L1 × L2]

  case class AssocLR[K: ProperKind, L: ProperKind, M: ProperKind]() extends Routing[(K × L) × M, K × (L × M)]

  case class AssocRL[K, L, M]()(using
    val K: ProperKind[K],
    val L: ProperKind[L],
    val M: ProperKind[M],
  ) extends Routing[K × (L × M), (K × L) × M]

  case class Swap[K: ProperKind, L: ProperKind]() extends Routing[K × L, L × K]

  case class Elim[K: ProperKind]() extends Routing[K, ○]

  case class ElimFst[K: ProperKind, L: ProperKind]() extends Routing[K × L, L]

  case class ElimSnd[K: ProperKind, L: ProperKind]() extends Routing[K × L, K]

  case class Dup[K]()(using val kind: OutputKind[K]) extends Routing[K, K × K]

  sealed trait AppTransRes[F[_, _], K, L]:
    type X
    def f: Routing[K, X]
    def g: PartialArgs[F, X, L]

  object AppTransRes {
    case class Impl[F[_, _], K, Y, L](
      f: Routing[K, Y],
      g: PartialArgs[F, Y, L],
    ) extends AppTransRes[F, K, L] {
      override type X = Y
    }

    def apply[F[_, _], K, Y, L](
      f: Routing[K, Y],
      g: PartialArgs[F, Y, L],
    ): AppTransRes[F, K, L] =
      Impl(f, g)
  }

  def id[K: Kind]: Routing[K, K] =
    Id()

  def par[K1: ProperKind, K2: ProperKind, L1: ProperKind, L2: ProperKind](
    f1: Routing[K1, L1],
    f2: Routing[K2, L2],
  ): Routing[K1 × K2, L1 × L2] =
    Par(f1, f2)

  def fst[K: ProperKind, L: ProperKind, M: ProperKind](f: Routing[K, L]): Routing[K × M, L × M] =
    par(f, Id())

  def snd[K: ProperKind, L: ProperKind, M: ProperKind](f: Routing[L, M]): Routing[K × L, K × M] =
    par(Id(), f)

  def assocLR[K: ProperKind, L: ProperKind, M: ProperKind]: Routing[(K × L) × M, K × (L × M)] =
    AssocLR()

  def assocRL[K: ProperKind, L: ProperKind, M: ProperKind]: Routing[K × (L × M), (K × L) × M] =
    AssocRL()

  def swap[K: ProperKind, L: ProperKind]: Routing[K × L, L × K] =
    Swap()

  def elimFst[K: ProperKind, L: ProperKind]: Routing[K × L, L] =
    ElimFst()

  def elimSnd[K: ProperKind, L: ProperKind]: Routing[K × L, K] =
    ElimSnd()

  def dup[K: ProperKind]: Routing[K, K × K] =
    ProperKind[K] match {
      case ProperKind.Type =>
        Dup()(using OutputKind[●])
      case ProperKind.Prod(k1, k2) =>
        def go[K1, K2](using k1: ProperKind[K1], k2: ProperKind[K2]): Routing[K1 × K2, (K1 × K2) × (K1 × K2)] =
          par(dup[K1], dup[K2]) > ixi
        go(using k1, k2)
    }

  def ixi[K1: ProperKind, K2: ProperKind, K3: ProperKind, K4: ProperKind]: Routing[(K1 × K2) × (K3 × K4), (K1 × K3) × (K2 × K4)] =
    assocLR[K1, K2, K3 × K4] > snd(assocRL[K2, K3, K4] > fst(swap) > assocLR) > assocRL

  def elim[K](using k: Kind[K]): Routing[K, ○] =
    k.properKind match {
      case Left(k_eq_○) => id[K].to(using k_eq_○)
      case Right(k)     => Elim[K]()(using k)
    }

  def proveId[K](r: Routing[○, K]): K =:= ○ =
    r match {
      case Id() =>
        implicitly[K =:= ○]
      case AndThen(p, q) =>
        proveId(proveId(p).substituteCo[Routing[*, K]](q))
      case other =>
        throw new NotImplementedError(s"$other (${summon[SourcePos]})")
    }
}
