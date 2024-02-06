package libretto.typology.types

import libretto.lambda.util.TypeEq
import libretto.lambda.util.TypeEq.Refl
import libretto.typology.kinds.*

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
}
