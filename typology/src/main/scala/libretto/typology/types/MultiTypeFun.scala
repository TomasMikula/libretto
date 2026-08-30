package libretto.typology.types

import libretto.lambda.UnhandledCase
import libretto.lambda.util.TypeEq
import libretto.lambda.util.TypeEq.Refl
import libretto.typology.kinds.*
import libretto.lambda.NarrowSymmetricSemigroupalCategory

/** Type function with possibly multiple output types. */
sealed trait MultiTypeFun[TC[_, _], K, L] {
  def >[M](f: TypeFun[TC, L, M]): TypeFun[TC, K, M]
  def inFst[M](using KindN[K], KindN[M]): MultiTypeFun[TC, K × M, L × M]
  def inSnd[J](using KindN[J], KindN[K]): MultiTypeFun[TC, J × K, J × L]
}

object MultiTypeFun {
  case class Impl[TC[_, _], K, X, L](
    routing: Routing[K, X],
    args: PartialArgs[TypeExpr[TC, _, _], X, L]
  ) extends MultiTypeFun[TC, K, L] {
    override def >[M](f: TypeFun[TC, L, M]): TypeFun[TC, K, M] =
      f.applyTo(args) ∘ routing

    override def inFst[M](using KindN[K], KindN[M]): MultiTypeFun[TC, K × M, L × M] =
      args.inKind.nonEmpty match
        case Left(ev) =>
          Impl(Routing.elimFst[K, M], PartialArgs.introFst(args.from[○](using ev.flip)))
        case Right(x) =>
          given KindN[X] = x
          Impl(routing.inFst[M], args.inFst[M])

    override def inSnd[J](using KindN[J], KindN[K]): MultiTypeFun[TC, J × K, J × L] =
      args.inKind.nonEmpty match
        case Left(ev) =>
          Impl(Routing.elimSnd[J, K], PartialArgs.introSnd(args.from[○](using ev.flip)))
        case Right(x) =>
          given KindN[X] = x
          Impl(routing.inSnd[J], args.inSnd[J])
  }

  def apply[TC[_, _], J, K, L](
    r: Routing[J, K],
    args: PartialArgs[TypeExpr[TC, _, _], K, L],
  ): MultiTypeFun[TC, J, L] =
    Impl(r, args)

  def apply[TC[_, _], K, L](
    args: PartialArgs[TypeExpr[TC, _, _], K, L],
  ): MultiTypeFun[TC, K, L] =
    import args.inKind
    Impl(Routing.id[K], args)

  def apply[TC[_, _], K, L](t: TypeExpr[TC, K, L]): MultiTypeFun[TC, K, L] =
    import t.given
    Impl(Routing.id[K], PartialArgs(t))

  def apply[TC[_, _], K, L](f: TypeFun[TC, K, L]): MultiTypeFun[TC, K, L] =
    import f.expr.inKind
    import f.outKind
    Impl(f.pre, PartialArgs(f.expr))

  def fst[TC[_, _], K, L, M](f: TypeFun[TC, K, L])(using KindN[K], KindN[M]): MultiTypeFun[TC, K × M, L × M] =
    MultiTypeFun(f).inFst

  def snd[TC[_, _], K, L, M](f: TypeFun[TC, L, M])(using KindN[K], KindN[L]): MultiTypeFun[TC, K × L, K × M] =
    MultiTypeFun(f).inSnd

  def introFst[TC[_, _], K, L](f: TypeFun[TC, ○, K])(using KindN[L]): MultiTypeFun[TC, L, K × L] =
    given KindN[K] = KindN(f.outKind)
    val a = TypeFun.toExpr(f)
    Impl(Routing.id[L], PartialArgs.introFst(PartialArgs(a)))

  def introSnd[TC[_, _], K, L](f: TypeFun[TC, ○, L])(using KindN[K]): MultiTypeFun[TC, K, K × L] =
    given KindN[L] = KindN(f.outKind)
    val a = TypeFun.toExpr(f)
    Impl(Routing.id[K], PartialArgs.introSnd(PartialArgs(a)))

  def introBoth[TC[_, _], K, L](a: TypeExpr[TC, ○, K], b: TypeExpr[TC, ○, L]): MultiTypeFun[TC, ○, K × L] =
    import a.outKind
    import b.outKind
    Impl(Routing.id[○], PartialArgs.introBoth(PartialArgs(a), PartialArgs(b)))

  def introBoth[TC[_, _], K, L](f: TypeFun[TC, ○, K], g: TypeFun[TC, ○, L]): MultiTypeFun[TC, ○, K × L] =
    given KindN[K] = KindN(f.outKind)
    given KindN[L] = KindN(g.outKind)
    val a = TypeFun.toExpr(f)
    val b = TypeFun.toExpr(g)
    Impl(Routing.id[○], PartialArgs.introBoth(PartialArgs(a), PartialArgs(b)))

  def introBoth[TC[_, _], K, L](a: MultiTypeFun[TC, ○, K], b: MultiTypeFun[TC, ○, L]): MultiTypeFun[TC, ○, K × L] =
    (a, b) match
      case (Impl(r1, a1), Impl(r2, a2)) =>
        (Routing.proveId(r1), Routing.proveId(r2)) match
          case (TypeEq(Refl()), TypeEq(Refl())) =>
            Impl(Routing.id[○], PartialArgs.introBoth(a1, a2))

  def dup[TC[_, _], K](using KindN[K]): MultiTypeFun[TC, K, K × K] =
    Impl(Routing.dup[K], PartialArgs.Id())

  given [TC[_, _]] => NarrowSymmetricSemigroupalCategory[MultiTypeFun[TC, _, _], ×, KindN] =
    new NarrowSymmetricSemigroupalCategory[MultiTypeFun[TC, _, _], ×, KindN] {
      override def id[A](wa: KindN[A]): MultiTypeFun[TC, A, A] =
        given KindN[A] = wa
        MultiTypeFun(Routing.id[A], PartialArgs.Id())

      override def swap[A, B](wa: KindN[A], wb: KindN[B]): MultiTypeFun[TC, A × B, B × A] =
        given KindN[A] = wa
        given KindN[B] = wb
        given KindN[B × A] = wb × wa
        MultiTypeFun(Routing.swap[A, B], PartialArgs.Id())

      override def assocLR[A, B, C](wa: KindN[A], wb: KindN[B], wc: KindN[C]): MultiTypeFun[TC, (A × B) × C, A × (B × C)] =
        given KindN[A] = wa
        given KindN[B] = wb
        given KindN[C] = wc
        given KindN[A × (B × C)] = wa × (wb × wc)
        MultiTypeFun(Routing.assocLR[A, B, C], PartialArgs.Id())

      override def assocRL[A, B, C](wa: KindN[A], wb: KindN[B], wc: KindN[C]): MultiTypeFun[TC, A × (B × C), (A × B) × C] =
        given KindN[A] = wa
        given KindN[B] = wb
        given KindN[C] = wc
        given KindN[(A × B) × C] = (wa × wb) × wc
        MultiTypeFun(Routing.assocRL[A, B, C], PartialArgs.Id())

      override def tensor[A, B](wa: KindN[A], wb: KindN[B]): KindN[A × B] =
        wa × wb

      override def par[A1, A2, B1, B2](f1: MultiTypeFun[TC, A1, B1], f2: MultiTypeFun[TC, A2, B2]): MultiTypeFun[TC, A1 × A2, B1 × B2] =
        (f1, f2) match
          case (Impl(r1, a1): Impl[TC, A1, x1, B1], Impl(r2, a2): Impl[TC, A2, x2, B2]) =>
            given KindN[A1] = r1.inKind.nonEmpty match { case Right(k) => k; case Left(_) => UnhandledCase.raise(s"$r1 used in par") }
            given KindN[A2] = r2.inKind.nonEmpty match { case Right(k) => k; case Left(_) => UnhandledCase.raise(s"$r2 used in par") }
            given KindN[x1] = a1.inKind.nonEmpty match { case Right(k) => k; case Left(_) => UnhandledCase.raise(s"$a1 used in par") }
            given KindN[x2] = a2.inKind.nonEmpty match { case Right(k) => k; case Left(_) => UnhandledCase.raise(s"$a2 used in par") }
            MultiTypeFun(Routing.par[A1, A2, x1, x2](r1, r2), PartialArgs.par(a1, a2))

      override def andThen[A, B, C](f: MultiTypeFun[TC, A, B], g: MultiTypeFun[TC, B, C]): MultiTypeFun[TC, A, C] =
        (f, g) match
          case (Impl(rf, af), Impl(rg, ag)) =>
            rg.applyTo(af) match
              case Routing.AppRes.Impl(p, a) =>
                val absorbL = [j, k, l] => (args: PartialArgs[TypeExpr[TC, _, _], j, k], t: TypeExpr[TC, k, l]) => t.applyTo(args)
                MultiTypeFun(rf > p, (a > ag)(absorbL))
    }
}
