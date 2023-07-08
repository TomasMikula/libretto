package libretto.typology.toylang.types

import libretto.lambda.{MappedMorphism, MonoidalObjectMap, SymmetricMonoidalCategory}
import libretto.lambda.util.SourcePos
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

  def snd[X](using ProperKind[X], ProperKind[K], ProperKind[L]): Routing[X × K, X × L] =
    Routing.snd(this)

  def applyTo[TA[_], J](args: ArgIntro[TA, J, K]): ApplyRes[TA, J, ?, L] = {
    import args.inKind

    this match {
      case Id() =>
        ApplyRes(Id(), args)

      case AndThen(f, g) =>
        f.applyTo(args) match {
          case ApplyRes(f1, args1) =>
            g.applyTo(args1) match {
              case ApplyRes(g1, args2) => ApplyRes(f1 > g1, args2)
            }
        }

      case p: Par[k1, k2, l1, l2] =>
        given ProperKind[l1] = Kind.fst(p.outKind)
        given ProperKind[l2] = Kind.snd(p.outKind)

        def go[K1, K2, L1: ProperKind, L2: ProperKind](
          args: ArgIntro[TA, J, K1 × K2],
          g1: Routing[K1, L1],
          g2: Routing[K2, L2],
        ): ApplyRes[TA, J, ?, L1 × L2] =
          args match {
            case i1: ArgIntro.IntroFst[TA, K1, J, K2] =>
              given ProperKind[J] = i1.properInKind
              val j1 = g1.applyTo0(i1.args)
              g2.applyTo(i1.f) match {
                case ApplyRes(r, j2) =>
                  r.outKind.properKind match {
                    case Left(_eq_○) => ApplyRes(Elim(), ArgIntro.introBoth(j1, j2.from(using _eq_○.flip)))
                    case Right(k)    => ApplyRes(r, ArgIntro.introFst(j1, j2)(using k))
                  }
              }
            case p @ ArgIntro.Par(f1, f2) =>
              def go[J1: ProperKind, J2: ProperKind](f1: ArgIntro[TA, J1, K1], f2: ArgIntro[TA, J2, K2]): ApplyRes[TA, J1 × J2, ?, L1 × L2] =
                ApplyRes.par(g1.applyTo(f1), g2.applyTo(f2))
              go(f1, f2)(using Kind.fst(p.inKind), Kind.snd(p.inKind))
            case other =>
              throw new NotImplementedError(s"$other (${summon[SourcePos]})")
          }

        go[k1, k2, l1, l2](args, p.f1, p.f2)

      case lr: AssocLR[k1, k2, k3] =>
        def go[K1, K2, K3](args: ArgIntro[TA, J, (K1 × K2) × K3]): ArgIntro[TA, J, K1 × (K2 × K3)] = {
          given ProperKind[K1] = Kind.fst(Kind.fst(args.outKind.kind).kind)
          given ProperKind[K2] = Kind.snd(Kind.fst(args.outKind.kind).kind)
          given ProperKind[K3] = Kind.snd(args.outKind.kind)

          args match {
            case i1 @ ArgIntro.IntroFst(args1, f) =>
              given ProperKind[J] = i1.properInKind
              args1 match {
                case ArgIntro.IntroBoth(a, b) =>
                  ArgIntro.introFst(a, ArgIntro.introFst(b, f))
                case other =>
                  throw new NotImplementedError(s"$other (${summon[SourcePos]})")
              }
            case p @ ArgIntro.Par(f1, f2) =>
              def go[J1: ProperKind, J2: ProperKind](f1: ArgIntro[TA, J1, K1 × K2], f2: ArgIntro[TA, J2, K3]): ArgIntro[TA, J1 × J2, K1 × (K2 × K3)] =
                f1 match {
                  case ArgIntro.IntroFst(a, f12) =>
                    ArgIntro.introFst(a, ArgIntro.par(f12, f2))
                  case ArgIntro.IntroSnd(f11, b) =>
                    ArgIntro.par(f11, ArgIntro.introFst(b, f2))
                  case other =>
                    throw new NotImplementedError(s"$other (${summon[SourcePos]})")
                }
              go(f1, f2)(using Kind.fst(p.inKind), Kind.snd(p.inKind))
            case other =>
              throw new NotImplementedError(s"$other (${summon[SourcePos]})")
          }
        }

        ApplyRes(Id(), go[k1, k2, k3](args))

      case rl: AssocRL[k1, k2, k3] =>
        def go[K1, K2, K3](args: ArgIntro[TA, J, K1 × (K2 × K3)]): ArgIntro[TA, J, (K1 × K2) × K3] = {
          given ProperKind[K1] = Kind.fst(args.outKind.kind)
          given ProperKind[K2] = Kind.fst(Kind.snd(args.outKind.kind).kind)
          given ProperKind[K3] = Kind.snd(Kind.snd(args.outKind.kind).kind)

          args match {
            case ArgIntro.IntroFst(a, f) =>
              f match {
                case ArgIntro.Id() =>
                  ArgIntro.fst[TA, K2, K1 × K2, K3](ArgIntro.introFst[TA, K1, K2](a))
                case p @ ArgIntro.Par(f1, f2) =>
                  def go[J1: ProperKind, J2: ProperKind](f1: ArgIntro[TA, J1, K2], f2: ArgIntro[TA, J2, K3]): ArgIntro[TA, J1 × J2, (K1 × K2) × K3] =
                    ArgIntro.par(ArgIntro.introFst(a, f1), f2)
                  go(f1, f2)(using Kind.fst(p.inKind), Kind.snd(p.inKind))
                case other =>
                  throw new NotImplementedError(s"$other (${summon[SourcePos]})")
              }
            case other =>
              throw new NotImplementedError(s"$other (${summon[SourcePos]})")
          }
        }

        ApplyRes(Id(), go[k1, k2, k3](args))

      case d @ Dup() =>
        given OutputKind[K] = d.kind
        args match {
          case ArgIntro.Id() =>
            ApplyRes(Dup[K](), ArgIntro.Id())
          case other =>
            throw new NotImplementedError(s"$other (${summon[SourcePos]})")
        }

      case Swap() =>
        args match {
          case i1 @ ArgIntro.IntroFst(a, f) =>
            given ProperKind[J] = i1.properInKind
            ApplyRes(Id(), ArgIntro.introSnd(f, a))
          case other =>
            throw new NotImplementedError(s"$other (${summon[SourcePos]})")
        }

      case ElimSnd() =>
        args match {
          case ArgIntro.IntroFst(a, _) =>
            ApplyRes(Routing.elim[J], a)
          case other =>
            throw new NotImplementedError(s"$other (${summon[SourcePos]})")
        }

      case other =>
        throw new NotImplementedError(s"applying $other to $args (${summon[SourcePos]})")
    }
  }

  def applyTo0[TA[_]](args: ArgIntro[TA, ○, K]): ArgIntro[TA, ○, L] = {
    this match {
      case Id() => args
      case AndThen(f, g) => g.applyTo0(f.applyTo0(args))
      case Dup() => ArgIntro.introBoth(args, args)
      case other => throw new NotImplementedError(s"$other (${summon[SourcePos]})")
    }
  }

  def applyToTrans[F[_, _], J](f: ArgTrans[F, J, K]): AppTransRes[F, J, ?, L] = {
    import f.inKind

    this match {
      case Id() =>
        AppTransRes(Id(), f)
      case AndThen(p, q) =>
        p.applyToTrans(f) match {
          case AppTransRes(p, f) =>
            q.applyToTrans(f) match {
              case AppTransRes(q, f) =>
                AppTransRes(p > q, f)
            }
        }
      case p: Par[k1, k2, l1, l2] =>
        given ProperKind[k1] = Kind.fst(p.inKind)
        given ProperKind[k2] = Kind.snd(p.inKind)
        given ProperKind[l1] = Kind.fst(p.outKind)
        given ProperKind[l2] = Kind.snd(p.outKind)

        def go[K1: ProperKind, K2: ProperKind, L1: ProperKind, L2: ProperKind](
          f: ArgTrans[F, J, K1 × K2],
          g1: Routing[K1, L1],
          g2: Routing[K2, L2],
        ): AppTransRes[F, J, ?, L1 × L2] =
          f match {
            case ArgTrans.IntroFst(f1) =>
              AppTransRes(g2, ArgTrans.introFst(g1.applyToTrans0(f1)))
            case ArgTrans.IntroBoth(f1, f2) =>
              AppTransRes(id, ArgTrans.introBoth(g1.applyToTrans0(f1), g2.applyToTrans0(f2)))
            case other =>
              throw new NotImplementedError(s"$other (${summon[SourcePos]})")
          }

        go[k1, k2, l1, l2](f, p.f1, p.f2)
      case Dup() =>
        f.inKind.properKind match {
          case Left(j_eq_○) =>
            val f0: ArgTrans[F, ○, K] = j_eq_○.substituteCo[ArgTrans[F, *, K]](f)
            AppTransRes(id[J].to[○](using j_eq_○), ArgTrans.introBoth(f0, f0))
          case Right(j) =>
            given ProperKind[J] = j
            AppTransRes(dup[J], ArgTrans.par(f, f))
        }
      case ElimFst() =>
        f match {
          case ArgTrans.IntroBoth(f1, f2) =>
            AppTransRes(id, f2)
          case other =>
            throw new NotImplementedError(s"$other (${summon[SourcePos]})")
        }
      case other =>
        throw new NotImplementedError(s"Applying $other to $f (${summon[SourcePos]})")
    }
  }

  def applyToTrans0[F[_, _]](f: ArgTrans[F, ○, K]): ArgTrans[F, ○, L] =
    applyToTrans(f) match {
      case AppTransRes(r, f) =>
        proveId(r).substituteCo[ArgTrans[F, *, L]](f)
    }

  def compile[==>[_, _], F[_, _], |*|[_, _], One, Q](fk: F[K, Q])(
    // tgt: TypeAlgebra[==>],
    // map_● : F[●, tgt.Type],
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
        throw NotImplementedError(s"at ${summon[SourcePos]}")
      case Par(f1, f2) =>
        throw NotImplementedError(s"at ${summon[SourcePos]}")
      case Elim() =>
        throw NotImplementedError(s"at ${summon[SourcePos]}")
      case Dup() =>
        throw NotImplementedError(s"at ${summon[SourcePos]}")
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

  case class AssocRL[K: ProperKind, L: ProperKind, M: ProperKind]() extends Routing[K × (L × M), (K × L) × M]

  case class Swap[K: ProperKind, L: ProperKind]() extends Routing[K × L, L × K]

  case class Elim[K: ProperKind]() extends Routing[K, ○]

  case class ElimFst[K: ProperKind, L: ProperKind]() extends Routing[K × L, L]

  case class ElimSnd[K: ProperKind, L: ProperKind]() extends Routing[K × L, K]

  case class Dup[K]()(using val kind: OutputKind[K]) extends Routing[K, K × K]

  case class ApplyRes[TA[_], K, X, L](r: Routing[K, X], ai: ArgIntro[TA, X, L]) {
    final type Pivot = X
  }
  object ApplyRes {
    def par[TA[_], K1, K2, X1, X2, L1, L2](
      a1: ApplyRes[TA, K1, X1, L1],
      a2: ApplyRes[TA, K2, X2, L2],
    )(using
      k1: ProperKind[K1],
      k2: ProperKind[K2],
      l1: ProperKind[L1],
      l2: ProperKind[L2],
    ): ApplyRes[TA, K1 × K2, ?, L1 × L2] =
      (a1.r.outKind.properKind, a2.r.outKind.properKind) match {
        case (Left(x1_eq_○), Left(x2_eq_○)) =>
          ApplyRes(Elim(), ArgIntro.introBoth(a1.ai.from(using x1_eq_○.flip), a2.ai.from(using x2_eq_○.flip)))
        case (Left(x1_eq_○), Right(x2)) =>
          ApplyRes(ElimFst[K1, K2]() > a2.r, ArgIntro.introFst(a1.ai.from(using x1_eq_○.flip), a2.ai)(using x2))
        case (Right(x1), Left(x2_eq_○)) =>
          ApplyRes(ElimSnd[K1, K2]() > a1.r, ArgIntro.introSnd(a1.ai, a2.ai.from(using x2_eq_○.flip))(using x1))
        case (Right(x1), Right(x2)) =>
          given ProperKind[X1] = x1
          given ProperKind[X2] = x2
          ApplyRes(Routing.par(a1.r, a2.r), ArgIntro.par(a1.ai, a2.ai))
      }
  }

  case class AppTransRes[F[_, _], K, X, L](f: Routing[K, X], g: ArgTrans[F, X, L])

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
