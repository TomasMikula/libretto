package libretto.typology.toylang.types

import libretto.lambda.{MappedMorphism, MonoidalObjectMap}
import libretto.typology.kinds._

sealed trait TypeFun[V, K, L] {
  type X
  val pre: Routing[K, X]
  val expr: TypeExpr[V, X, L]

  given inKind: Kind[K] = pre.inKind
  given outKind: OutputKind[L] = expr.outKind

  def ∘[J](that: TypeFun[V, J, K]): TypeFun[V, J, L] = {
    import that.pre.outKind
    import that.expr.outKind

    this.pre.applyToTrans[TypeExpr[V, _, _], that.X](ArgTrans(that.expr)) match {
      case Routing.AppTransRes.Impl(q, e) =>
        TypeFun(that.pre > q, this.expr.transCompose(e))
    }
  }

  def apply(t: TypeExpr[V, ○, K]): TypeExpr[V, ○, L] =
    TypeFun.toExpr(this ∘ TypeFun.fromExpr(t))

  def compile[==>[_, _], F[_, _], Q](
    tgt: TypeAlgebra[V, ==>],
    fk: F[K, Q],
    map_● : F[●, tgt.Type],
    dupTypes: [k, q] => F[k, q] => (q ==> tgt.<*>[q, q]),
  )(using
    F: MonoidalObjectMap[F, ×, ○, tgt.<*>, tgt.None],
  ): MappedMorphism[==>, F, K, L] = {
    import tgt.given
    val pre1 = pre.compile[==>, F, tgt.<*>, tgt.None, Q](fk)(dupTypes)
    pre1 > expr.compile(tgt, pre1.tgtMap, map_●)
  }

  def vmap[W](f: V => W): TypeFun[W, K, L] =
    TypeFun(pre, expr.vmap(f))
}

object TypeFun {
  def apply[V, K, P, L](r: Routing[K, P], f: TypeExpr[V, P, L]): TypeFun[V, K, L] =
    new TypeFun[V, K, L] {
      override type X = P
      override val pre = r
      override val expr = f
    }

  def unapply[V, K, L](f: TypeFun[V, K, L]): (Routing[K, f.X], TypeExpr[V, f.X, L]) =
    (f.pre, f.expr)

  def fromExpr[V, K, L](e: TypeExpr[V, K, L]): TypeFun[V, K, L] = {
    import e.inKind
    TypeFun(Routing.id[K], e)
  }

  def toExpr[V, L](f: TypeFun[V, ○, L]): TypeExpr[V, ○, L] =
    Routing.proveId(f.pre).substituteCo[TypeExpr[V, _, L]](f.expr)

  def unit[V]: TypeFun[V, ○, ●] =
    fromExpr(TypeExpr.unit)

  def int[V]: TypeFun[V, ○, ●] =
    fromExpr(TypeExpr.int)

  def string[V]: TypeFun[V, ○, ●] =
    fromExpr(TypeExpr.string)

  def pair[V]: TypeFun[V, ● × ●, ●] =
    fromExpr(TypeExpr.pair)

  def pair[V](a: TypeFun[V, ○, ●], b: TypeFun[V, ○, ●]): TypeFun[V, ○, ●] =
    fromExpr(TypeExpr.pair(toExpr(a), toExpr(b)))

  def pair1[V](a: Type[V]): TypeFun[V, ●, ●] =
    fromExpr(TypeExpr.pair1(a))

  def pair1[V](a: TypeFun[V, ○, ●]): TypeFun[V, ●, ●] =
    pair1(toExpr(a))

  def sum[V]: TypeFun[V, ● × ●, ●] =
    fromExpr(TypeExpr.sum)

  def sum[V](a: TypeFun[V, ○, ●], b: TypeFun[V, ○, ●]): TypeFun[V, ○, ●] =
    fromExpr(TypeExpr.sum(toExpr(a), toExpr(b)))

  def sum1[V](a: Type[V]): TypeFun[V, ●, ●] =
    fromExpr(TypeExpr.sum1(a))

  def sum1[V](a: TypeFun[V, ○, ●]): TypeFun[V, ●, ●] =
    sum1(toExpr(a))

  def fix[V](f: TypeFun[V, ●, ●]): TypeFun[V, ○, ●] =
    f match {
      case TypeFun(pre, expr) => fromExpr(TypeExpr.fix(pre, expr))
    }

  def pfix[V](f: TypeFun[V, ● × ●, ●]): TypeFun[V, ●, ●] =
    f match {
      case TypeFun(pre, expr) => fromExpr(TypeExpr.pfix(pre, expr))
    }

  def composeSnd[V, K, L, M, N](g: TypeFun[V, K × M, N], f: TypeFun[V, L, M])(using
    ProperKind[L],
  ): TypeFun[V, K × L, N] = {
    def go[X, Y](f1: Routing[L, X], f2: TypeExpr[V, X, M], g1: Routing[K × M, Y], g2: TypeExpr[V, Y, N]): TypeFun[V, K × L, N] = {
      given ProperKind[K] = Kind.fst(g.inKind)
      given OutputKind[M] = f2.outKind

      f2.inKind.properKind match {
        case Left(x_eq_○) =>
          val f20: TypeExpr[V, ○, M] = x_eq_○.substituteCo[TypeExpr[V, _, M]](f2)
          g1.applyToTrans(ArgTrans.introSnd(ArgTrans(f20))) match {
            case Routing.AppTransRes.Impl(g1, f21) =>
              TypeFun(Routing.elimSnd[K, L] > g1, g2.transCompose(f21))
          }
        case Right(given ProperKind[X]) =>
          g1.applyToTrans(ArgTrans(f2).inSnd[K]) match {
            case Routing.AppTransRes.Impl(g1, f2) =>
              TypeFun(f1.snd[K] > g1, g2.transCompose(f2))
          }
      }
    }

    (f, g) match {
      case (TypeFun(f1, f2), TypeFun(g1, g2)) =>
        go(f1, f2, g1, g2)
    }
  }

  def appFst[V, K, L, M](f: TypeFun[V, K × L, M], a: TypeFun[V, ○, K]): TypeFun[V, L, M] = {
    given OutputKind[K] = a.outKind
    given ProperKind[L] = Kind.snd(f.inKind)

    def go[X](a: TypeExpr[V, ○, K], f1: Routing[K × L, X], f2: TypeExpr[V, X, M]): TypeFun[V, L, M] = {
      f1.applyToTrans(ArgTrans.introFst(ArgTrans(a))) match {
        case Routing.AppTransRes.Impl(f0, args) =>
          TypeFun(f0, f2.transCompose(args))
      }
    }

    f match {
      case TypeFun(f1, f2) => go(TypeFun.toExpr(a), f1, f2)
    }
  }

  def abstractType[V](name: V): TypeFun[V, ○, ●] =
    fromExpr(TypeExpr.abstractType(name))
}
