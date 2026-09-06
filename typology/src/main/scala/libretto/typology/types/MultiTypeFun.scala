package libretto.typology.types

import libretto.lambda.util.{Exists, TypeEq}
import libretto.lambda.util.Exists.Indeed
import libretto.lambda.util.TypeEq.Refl
import libretto.typology.kinds.*
import libretto.lambda.{NarrowSymmetricSemigroupalCategory, NarrowSymmetricWSemigroupalCategory}

/** Type function with possibly multiple output types. */
sealed trait MultiTypeFun[TC[_, _], K, L] {
  def >[M](f: MultiTypeFun[TC, L, M]): MultiTypeFun[TC, K, M] = MultiTypeFun.andThen(this, f)
  def >[M](f: TypeFun[TC, L, M]): TypeFun[TC, K, M]
  def inFst[M](using KindN[K], KindN[L], KindN[M]): MultiTypeFun[TC, K × M, L × M]
  def inSnd[J](using KindN[J], KindN[K], KindN[L]): MultiTypeFun[TC, J × K, J × L]

  def to[M](using L =:= M): MultiTypeFun[TC, K, M] =
    summon[L =:= M].substituteCo(this)

  def from[J](using J =:= K): MultiTypeFun[TC, J, L] =
    summon[J =:= K].substituteContra[[x] =>> MultiTypeFun[TC, x, L]](this)
}

object MultiTypeFun {
  case class RoutingOnly[TC[_, _], K, L](
    routing: Routing[K, L],
  ) extends MultiTypeFun[TC, K, L] {
    override def >[M](f: TypeFun[TC, L, M]): TypeFun[TC, K, M] =
      f ∘ routing

    override def inFst[M](using KindN[K], KindN[L], KindN[M]): MultiTypeFun[TC, K × M, L × M] =
      RoutingOnly(routing.inFst[M])

    override def inSnd[J](using KindN[J], KindN[K], KindN[L]): MultiTypeFun[TC, J × K, J × L] =
      RoutingOnly(routing.inSnd[J])
  }

  case class Proper[TC[_, _], K, X, L](
    routing: Routing[K, X],
    args: PartialArgs.Proper[TypeExpr[TC, _, _], X, L]
  ) extends MultiTypeFun[TC, K, L] {
    override def >[M](f: TypeFun[TC, L, M]): TypeFun[TC, K, M] =
      f.applyTo(args) ∘ routing

    override def inFst[M](using KindN[K], KindN[L], KindN[M]): MultiTypeFun[TC, K × M, L × M] =
      args.inKind.nonEmpty match
        case Left(ev) =>
          MultiTypeFun(Routing.elimFst[K, M], PartialArgs.introFst(args.from[○](using ev.flip)))
        case Right(x) =>
          given KindN[X] = x
          MultiTypeFun(routing.inFst[M], args.inFst[M])

    override def inSnd[J](using KindN[J], KindN[K], KindN[L]): MultiTypeFun[TC, J × K, J × L] =
      args.inKind.nonEmpty match
        case Left(ev) =>
          MultiTypeFun(Routing.elimSnd[J, K], PartialArgs.introSnd(args.from[○](using ev.flip)))
        case Right(x) =>
          given KindN[X] = x
          MultiTypeFun(routing.inSnd[J], args.inSnd[J])
  }

  def apply[TC[_, _], J, K, L](
    r: Routing[J, K],
    args: PartialArgs[TypeExpr[TC, _, _], K, L],
  ): MultiTypeFun[TC, J, L] =
    args match
      case _: PartialArgs.Id[f, k] => RoutingOnly(r)
      case args: PartialArgs.Proper[f, k, l] => Proper(r, args)

  def apply[TC[_, _], K, L](
    args: PartialArgs[TypeExpr[TC, _, _], K, L],
  ): MultiTypeFun[TC, K, L] =
    import args.inKind
    args match
      case _: PartialArgs.Id[f, k] => RoutingOnly(Routing.id[K])
      case args: PartialArgs.Proper[f, k, l] => Proper(Routing.id[K], args)

  def apply[TC[_, _], K, L](t: TypeExpr[TC, K, L]): MultiTypeFun[TC, K, L] =
    import t.given
    Proper(Routing.id[K], PartialArgs(t))

  def apply[TC[_, _], K, L](f: TypeFun[TC, K, L]): MultiTypeFun[TC, K, L] =
    import f.expr.inKind
    import f.outKind
    Proper(f.pre, PartialArgs(f.expr))

  private def id[TC[_, _], K](using k: Kinds[K]): MultiTypeFun[TC, K, K] =
    RoutingOnly(Routing.id[K])

  def fst[TC[_, _], K, L, M](f: TypeFun[TC, K, L])(using KindN[K], KindN[L], KindN[M]): MultiTypeFun[TC, K × M, L × M] =
    MultiTypeFun(f).inFst

  def snd[TC[_, _], K, L, M](f: TypeFun[TC, L, M])(using KindN[K], KindN[L], KindN[M]): MultiTypeFun[TC, K × L, K × M] =
    MultiTypeFun(f).inSnd

  def introFst[TC[_, _], K, L](f: MultiTypeFun[TC, ○, K])(using k: KindN[K], l: KindN[L]): MultiTypeFun[TC, L, K × L] =
    val f1 = MultiTypeFun.extract(f)
    Proper(Routing.id[L](using Kinds(l)), PartialArgs.introFst(f1))

  def introFst[TC[_, _], K, L](f: TypeFun[TC, ○, K])(using KindN[L]): MultiTypeFun[TC, L, K × L] =
    given KindN[K] = KindN(f.outKind)
    val a = TypeFun.toExpr(f)
    Proper(Routing.id[L], PartialArgs.introFst(PartialArgs(a)))

  def introSnd[TC[_, _], K, L](f: MultiTypeFun[TC, ○, L])(using k: KindN[K], l: KindN[L]): MultiTypeFun[TC, K, K × L] =
    val f2 = MultiTypeFun.extract(f)
    Proper(Routing.id[K](using Kinds(k)), PartialArgs.introSnd(f2))

  def introSnd[TC[_, _], K, L](f: TypeFun[TC, ○, L])(using KindN[K]): MultiTypeFun[TC, K, K × L] =
    given KindN[L] = KindN(f.outKind)
    val a = TypeFun.toExpr(f)
    Proper(Routing.id[K], PartialArgs.introSnd(PartialArgs(a)))

  def introBoth[TC[_, _], K, L](a: TypeExpr[TC, ○, K], b: TypeExpr[TC, ○, L]): MultiTypeFun[TC, ○, K × L] =
    import a.outKind
    import b.outKind
    Proper(Routing.id[○], PartialArgs.introBoth(PartialArgs(a), PartialArgs(b)))

  def introBoth[TC[_, _], K, L](f: TypeFun[TC, ○, K], g: TypeFun[TC, ○, L]): MultiTypeFun[TC, ○, K × L] =
    given KindN[K] = KindN(f.outKind)
    given KindN[L] = KindN(g.outKind)
    val a = TypeFun.toExpr(f)
    val b = TypeFun.toExpr(g)
    Proper(Routing.id[○], PartialArgs.introBoth(PartialArgs(a), PartialArgs(b)))

  def introBoth[TC[_, _], K, L](a: MultiTypeFun[TC, ○, K], b: MultiTypeFun[TC, ○, L])(using
    KindN[K],
    KindN[L],
  ): MultiTypeFun[TC, ○, K × L] =
    (a, b) match
      case (p1: Proper[TC, o1, x1, k], p2: Proper[TC, o2, x2, l]) =>
        (Routing.proveId(p1.routing), Routing.proveId(p2.routing)) match
          case (TypeEq(Refl()), TypeEq(Refl())) =>
            Proper(Routing.id[○], PartialArgs.introBoth(p1.args, p2.args))
      case (r: RoutingOnly[TC, ○, K], _) =>
        KindN.cannotBeUnit(Routing.proveId(r.routing).substituteCo[KindN](summon[KindN[K]]))
      case (_, r: RoutingOnly[TC, ○, L]) =>
        KindN.cannotBeUnit(Routing.proveId(r.routing).substituteCo[KindN](summon[KindN[L]]))

  def elim[TC[_, _], K](using k: Kinds[K]): MultiTypeFun[TC, K, ○] =
    RoutingOnly(Routing.elim[K])

  def elimFst[TC[_, _], K, L](using KindN[K], KindN[L]): MultiTypeFun[TC, K × L, L] =
    RoutingOnly(Routing.elimFst[K, L])

  def elimFst[TC[_, _], K, L, P](p: Kinds.Prod[K, L, P]): MultiTypeFun[TC, P, L] =
    import libretto.typology.kinds.Kinds.Prod.*
    p match
      case UnitUnit     => summon[P =:= ○]; elim[TC, P](using p.outKinds)
      case LeftUnit(l)  => summon[P =:= L]; id[TC, L](using Kinds(l))
      case RightUnit(k) => summon[P =:= K]; elim[TC, K](using Kinds(k))
      case Both(k, l)   => elimFst(using k, l)

  def elimSnd[TC[_, _], K, L](using KindN[K], KindN[L]): MultiTypeFun[TC, K × L, K] =
    RoutingOnly(Routing.elimSnd[K, L])

  def elimSnd[TC[_, _], K, L, P](p: Kinds.Prod[K, L, P]): MultiTypeFun[TC, P, K] =
    import libretto.typology.kinds.Kinds.Prod.*
    p match
      case UnitUnit     => summon[P =:= ○]; elim[TC, P](using p.outKinds)
      case LeftUnit(l)  => summon[P =:= L]; elim[TC, L](using Kinds(l))
      case RightUnit(k) => summon[P =:= K]; id[TC, K](using Kinds(k))
      case Both(k, l)   => elimSnd(using k, l)

  def dup[TC[_, _], K](using KindN[K]): MultiTypeFun[TC, K, K × K] =
    RoutingOnly(Routing.dup[K])

  def par[TC[_, _], A1, A2, B1, B2](
    f1: MultiTypeFun[TC, A1, B1],
    f2: MultiTypeFun[TC, A2, B2],
  )(using
    KindN[A1], KindN[A2], KindN[B1], KindN[B2],
  ): MultiTypeFun[TC, A1 × A2, B1 × B2] =
    (f1, f2) match
      case (r1: RoutingOnly[TC, a1, b1], r2: RoutingOnly[TC, a2, b2]) =>
        RoutingOnly(Routing.par[A1, A2, B1, B2](r1.routing, r2.routing))
      case (r1: RoutingOnly[TC, a1, b1], p2: Proper[TC, a2, x2, b2]) =>
        p2.args.inKind.nonEmpty match
          case Right(x2) =>
            given KindN[x2] = x2
            MultiTypeFun(Routing.par[A1, A2, B1, x2](r1.routing, p2.routing), p2.args.inSnd[B1])
          case Left(TypeEq(Refl())) =>
            MultiTypeFun(Routing.elimSnd[A1, A2] > r1.routing, PartialArgs.introSnd(p2.args))
      case (p1: Proper[TC, a1, x1, b1], r2: RoutingOnly[TC, a2, b2]) =>
        p1.args.inKind.nonEmpty match
          case Right(x1) =>
            given KindN[x1] = x1
            MultiTypeFun(Routing.par[A1, A2, x1, B2](p1.routing, r2.routing), p1.args.inFst[B2])
          case Left(TypeEq(Refl())) =>
            MultiTypeFun(Routing.elimFst[A1, A2] > r2.routing, PartialArgs.introFst(p1.args))
      case (p1: Proper[TC, a1, x1, b1], p2: Proper[TC, a2, x2, b2]) =>
        p1.args.inKind.nonEmpty match
          case Right(x1) =>
            p2.args.inKind.nonEmpty match
              case Right(x2) =>
                given KindN[x1] = x1
                given KindN[x2] = x2
                MultiTypeFun(Routing.par[A1, A2, x1, x2](p1.routing, p2.routing), PartialArgs.par(p1.args, p2.args))
              case Left(TypeEq(Refl())) =>
                MultiTypeFun(Routing.elimSnd[A1, A2] > p1.routing, PartialArgs.introSnd(p1.args, p2.args))
          case Left(TypeEq(Refl())) =>
            p2.args.inKind.nonEmpty match
              case Right(x2) =>
                MultiTypeFun(Routing.elimFst[A1, A2] > p2.routing, PartialArgs.introFst(p1.args, p2.args))
              case Left(TypeEq(Refl())) =>
                MultiTypeFun(Routing.elim[A1 × A2], PartialArgs.introBoth(p1.args, p2.args))

  def wpar[TC[_, _], A1, A2, B1, B2](
    f1: MultiTypeFun[TC, A1, B1],
    f2: MultiTypeFun[TC, A2, B2],
  )[P, Q](
    pSrc: Kinds.Prod[A1, A2, P],
    pTgt: Kinds.Prod[B1, B2, Q],
  ): MultiTypeFun[TC, P, Q] = {
    import Kinds.Prod.*

    pTgt match
      case UnitUnit =>
        elim(using pSrc.outKinds)
      case LeftUnit(_) =>
        elimFst(pSrc) > f2
      case RightUnit(_) =>
        elimSnd(pSrc) > f1
      case Both(b1, b2) =>
        given KindN[B1] = b1
        given KindN[B2] = b2
        pSrc match
          case UnitUnit      => introBoth(f1, f2)(using b1, b2)
          case LeftUnit(a2)  => summon[A1 =:= ○]; given KindN[A2] = a2; introFst(f1)(using b1, a2) > f2.inSnd[B1]
          case RightUnit(a1) => summon[A2 =:= ○]; given KindN[A1] = a1; introSnd(f2)(using a1, b2) > f1.inFst[B2]
          case Both(a1, a2)  => par(f1, f2)(using a1, a2, b1, b2)
  }

  def andThen[TC[_, _], A, B, C](
    f: MultiTypeFun[TC, A, B],
    g: MultiTypeFun[TC, B, C],
  ): MultiTypeFun[TC, A, C] =
    (f, g) match
      case (r1: RoutingOnly[TC, a, b], r2: RoutingOnly[TC, b2, c]) =>
        RoutingOnly(r1.routing > r2.routing)
      case (r1: RoutingOnly[TC, a, b], p2: Proper[TC, b2, x2, c]) =>
        Proper(r1.routing > p2.routing, p2.args)
      case (p1: Proper[TC, a, x1, b], r2: RoutingOnly[TC, b2, c]) =>
        r2.routing.applyTo(p1.args) match
          case Routing.AppRes.Impl(p, a) =>
            MultiTypeFun(p1.routing > p, a)
      case (p1: Proper[TC, a, x1, b], p2: Proper[TC, b2, x2, c]) =>
        p2.routing.applyTo(p1.args) match
          case Routing.AppRes.Impl(p, a) =>
            val absorbL = [j, k, l] => (args: PartialArgs[TypeExpr[TC, _, _], j, k], t: TypeExpr[TC, k, l]) => t.applyTo(args)
            MultiTypeFun(p1.routing > p, (a > p2.args)(absorbL))

  private def wswap_[TC[_, _], A, B, P](
    p: Kinds.Prod[A, B, P],
  ): Exists[[Q] =>> (MultiTypeFun[TC, P, Q], Kinds.Prod[B, A, Q])] = {
    import Kinds.Prod.*
    p match {
      case UnitUnit =>
        Exists((id[TC, ○], UnitUnit))
      case RightUnit(ka) =>
        Exists((id[TC, A](using Kinds(ka)), LeftUnit(ka)))
      case LeftUnit(kb) =>
        Exists((id[TC, B](using Kinds(kb)), RightUnit(kb)))
      case Both(ka, kb) =>
        Exists((RoutingOnly(Routing.swap[A, B](using ka, kb)), Both(kb, ka)))
    }
  }

  def wswap[TC[_, _], A, B, P, Q](
    p: Kinds.Prod[A, B, P],
    q: Kinds.Prod[B, A, Q],
  ): MultiTypeFun[TC, P, Q] =
    wswap_[TC, A, B, P](p) match
      case Indeed((f, q1)) =>
        (q1 deriveEq q).substituteCo(f)

  private def wassocLR_[TC[_, _], A, B, C, AB, AB_C](
    pAB: Kinds.Prod[A, B, AB],
    pABC: Kinds.Prod[AB, C, AB_C],
  ): Exists[[BC] =>> Exists[[A_BC] =>> (MultiTypeFun[TC, AB_C, A_BC], Kinds.Prod[B, C, BC], Kinds.Prod[A, BC, A_BC])]] = {
    import Kinds.Prod.*
    pABC match {
      case UnitUnit =>
        summon[AB =:= ○]
        pAB.proveUnitInputs match
          case (TypeEq(Refl()), TypeEq(Refl())) =>
            Exists(Exists((id[TC, ○], UnitUnit, UnitUnit)))
      case LeftUnit(kc) =>
        summon[AB =:= ○]
        pAB.proveUnitInputs match
          case (TypeEq(Refl()), TypeEq(Refl())) =>
            Exists(Exists((id[TC, C](using Kinds(kc)), LeftUnit(kc), LeftUnit(kc))))
      case RightUnit(kab) =>
        summon[C =:= ○]
        Exists(Exists((id[TC, AB](using Kinds(kab)), rightUnit(pAB.inKinds2), pAB)))
      case Both(kab, kc) =>
        pAB match
          case Both(ka, kb) =>
            Exists(Exists((RoutingOnly(Routing.assocLR[A, B, C](using ka, kb, kc)), Both(kb, kc), Both(ka, kb × kc))))
          case LeftUnit(kb) =>
            Exists(Exists((id[TC, B × C](using Kinds(kb × kc)), Both(kb, kc), LeftUnit(kb × kc))))
          case RightUnit(ka) =>
            Exists(Exists((id[TC, A × C](using Kinds(ka × kc)), LeftUnit(kc), Both(ka, kc))))
          case UnitUnit =>
            KindN.cannotBeUnit(kab)
    }
  }

  def wassocLR[TC[_, _], A, B, C, AB, AB_C, BC, A_BC](
    pAB: Kinds.Prod[A, B, AB],
    pAB_C: Kinds.Prod[AB, C, AB_C],
    pBC: Kinds.Prod[B, C, BC],
    pA_BC: Kinds.Prod[A, BC, A_BC],
  ): MultiTypeFun[TC, AB_C, A_BC] =
    wassocLR_[TC, A, B, C, AB, AB_C](pAB, pAB_C) match
      case Indeed(Indeed((f, qBC, qA_BC))) =>
        qBC.deriveEq(pBC) match
          case TypeEq(Refl()) =>
            f.to[A_BC](using qA_BC.deriveEq(pA_BC))

  private def wassocRL_[TC[_, _], A, B, C, BC, A_BC](
    pBC: Kinds.Prod[B, C, BC],
    pA_BC: Kinds.Prod[A, BC, A_BC],
  ): Exists[[AB] =>> Exists[[AB_C] =>> (MultiTypeFun[TC, A_BC, AB_C], Kinds.Prod[A, B, AB], Kinds.Prod[AB, C, AB_C])]] = {
    import Kinds.Prod.*
    pA_BC match {
      case UnitUnit =>
        summon[BC =:= ○]
        pBC.proveUnitInputs match
          case (TypeEq(Refl()), TypeEq(Refl())) =>
            Exists(Exists((id[TC, ○], UnitUnit, UnitUnit)))
      case RightUnit(ka) =>
        summon[BC =:= ○]
        pBC.proveUnitInputs match
          case (TypeEq(Refl()), TypeEq(Refl())) =>
            Exists(Exists((id[TC, A](using Kinds(ka)), RightUnit(ka), RightUnit(ka))))
      case LeftUnit(kbc) =>
        summon[A =:= ○]
        Exists(Exists((id[TC, BC](using Kinds(kbc)), leftUnit(pBC.inKinds1), pBC)))
      case Both(ka, kbc) =>
        pBC match
          case Both(kb, kc) =>
            Exists(Exists((RoutingOnly(Routing.assocRL[A, B, C](using ka, kb, kc)), Both(ka, kb), Both(ka × kb, kc))))
          case LeftUnit(kc) =>
            Exists(Exists((id[TC, A × C](using Kinds(ka × kc)), RightUnit(ka), Both(ka, kc))))
          case RightUnit(kb) =>
            Exists(Exists((id[TC, A × B](using Kinds(ka × kb)), Both(ka, kb), RightUnit(ka × kb))))
          case UnitUnit =>
            KindN.cannotBeUnit(kbc)
    }
  }

  def wassocRL[TC[_, _], A, B, C, BC, A_BC, AB, AB_C](
    pBC: Kinds.Prod[B, C, BC],
    pA_BC: Kinds.Prod[A, BC, A_BC],
    pAB: Kinds.Prod[A, B, AB],
    pAB_C: Kinds.Prod[AB, C, AB_C],
  ): MultiTypeFun[TC, A_BC, AB_C] =
    wassocRL_[TC, A, B, C, BC, A_BC](pBC, pA_BC) match
      case Indeed(Indeed((f, qAB, qABC))) =>
        qAB.deriveEq(pAB) match
          case TypeEq(Refl()) =>
            f.to[AB_C](using qABC.deriveEq(pAB_C))

  def extract[TC[_, _], K](f: MultiTypeFun[TC, ○, K])(using k: KindN[K]): PartialArgs[TypeExpr[TC, _, _], ○, K] =
    f match
      case Proper(routing, args) => Routing.proveId(routing) match { case TypeEq(Refl()) => args }
      case RoutingOnly(routing) => Routing.proveId(routing) match { case TypeEq(Refl()) => KindN.cannotBeUnit(k) }

  given [TC[_, _]] => NarrowSymmetricSemigroupalCategory[KindN, MultiTypeFun[TC, _, _], ×] =
    new NarrowSymmetricSemigroupalCategory[KindN, MultiTypeFun[TC, _, _], ×] {
      override def id[A](using wa: KindN[A]): MultiTypeFun[TC, A, A] =
        given KindN[A] = wa
        RoutingOnly(Routing.id[A])

      override def swap[A, B](using wa: KindN[A], wb: KindN[B]): MultiTypeFun[TC, A × B, B × A] =
        RoutingOnly(Routing.swap[A, B])

      override def assocLR[A, B, C](using wa: KindN[A], wb: KindN[B], wc: KindN[C]): MultiTypeFun[TC, (A × B) × C, A × (B × C)] =
        RoutingOnly(Routing.assocLR[A, B, C])

      override def assocRL[A, B, C](using wa: KindN[A], wb: KindN[B], wc: KindN[C]): MultiTypeFun[TC, A × (B × C), (A × B) × C] =
        RoutingOnly(Routing.assocRL[A, B, C])

      override def tensor[A, B](wa: KindN[A], wb: KindN[B]): KindN[A × B] =
        wa × wb

      override def narrowPar[A1, A2, B1, B2](
        f1: MultiTypeFun[TC, A1, B1],
        f2: MultiTypeFun[TC, A2, B2],
      )(using
        a1: KindN[A1], a2: KindN[A2],
        b1: KindN[B1], b2: KindN[B2],
      ): MultiTypeFun[TC, A1 × A2, B1 × B2] =
        MultiTypeFun.par[TC, A1, A2, B1, B2](f1, f2)

      override def andThen[A, B, C](f: MultiTypeFun[TC, A, B], g: MultiTypeFun[TC, B, C]): MultiTypeFun[TC, A, C] =
        MultiTypeFun.andThen[TC, A, B, C](f, g)
    }

  given [TC[_, _]] => NarrowSymmetricWSemigroupalCategory[Kinds, MultiTypeFun[TC, _, _], Kinds.Prod] =
    new NarrowSymmetricWSemigroupalCategory[Kinds, MultiTypeFun[TC, _, _], Kinds.Prod] {
      override def id[A](using wa: Kinds[A]): MultiTypeFun[TC, A, A] =
        given Kinds[A] = wa
        RoutingOnly(Routing.id[A])

      override def wtensor[A, B, P](wa: Kinds[A], wb: Kinds[B])(p: Kinds.Prod[A, B, P]): Kinds[P] =
        p.outKinds

      override def wpar[A1, A2, B1, B2](
        f1: MultiTypeFun[TC, A1, B1],
        f2: MultiTypeFun[TC, A2, B2],
      )(using
        a1: Kinds[A1], a2: Kinds[A2],
        b1: Kinds[B1], b2: Kinds[B2],
      )[P, Q](
        pSrc: Kinds.Prod[A1, A2, P],
        pTgt: Kinds.Prod[B1, B2, Q],
      ): MultiTypeFun[TC, P, Q] =
        MultiTypeFun.wpar(f1, f2)(pSrc, pTgt)

      override def wassocLR[A, B, C](
        a: Kinds[A], b: Kinds[B], c: Kinds[C],
      )[AB, AB_C, BC, A_BC](
        pAB: Kinds.Prod[A, B, AB],
        pAB_C: Kinds.Prod[AB, C, AB_C],
        pBC: Kinds.Prod[B, C, BC],
        pA_BC: Kinds.Prod[A, BC, A_BC],
      ): MultiTypeFun[TC, AB_C, A_BC] =
        MultiTypeFun.wassocLR(pAB, pAB_C, pBC, pA_BC)

      override def wassocRL[A, B, C](
        a: Kinds[A], b: Kinds[B], c: Kinds[C],
      )[BC, A_BC, AB, AB_C](
        pBC: Kinds.Prod[B, C, BC],
        pA_BC: Kinds.Prod[A, BC, A_BC],
        pAB: Kinds.Prod[A, B, AB],
        pAB_C: Kinds.Prod[AB, C, AB_C],
      ): MultiTypeFun[TC, A_BC, AB_C] =
        MultiTypeFun.wassocRL(pBC, pA_BC, pAB, pAB_C)

      override def wswap[A, B](
        wa: Kinds[A], wb: Kinds[B],
      )[P, Q](
        p: Kinds.Prod[A, B, P],
        q: Kinds.Prod[B, A, Q],
      ): MultiTypeFun[TC, P, Q] =
        MultiTypeFun.wswap[TC, A, B, P, Q](p, q)

      override def tensorUniq[A, B, P, Q](p: Kinds.Prod[A, B, P], q: Kinds.Prod[A, B, Q]): P =:= Q =
        p deriveEq q

      override def andThen[A, B, C](f: MultiTypeFun[TC, A, B], g: MultiTypeFun[TC, B, C]): MultiTypeFun[TC, A, C] =
        MultiTypeFun.andThen[TC, A, B, C](f, g)
    }
}
