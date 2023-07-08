package libretto.typology.toylang.types

import libretto.lambda.{MappedMorphism, MonoidalObjectMap}
import libretto.typology.kinds._

sealed trait TypeFun[K, L] {
  type X
  val pre: Routing[K, X]
  val expr: TypeExpr[X, L]

  given inKind: Kind[K] = pre.inKind
  given outKind: OutputKind[L] = expr.outKind

  def ∘[J](that: TypeFun[J, K]): TypeFun[J, L] = {
    import that.pre.outKind
    import that.expr.outKind

    this.pre.applyToTrans[TypeExpr[*, *], that.X](ArgTrans(that.expr)) match {
      case Routing.AppTransRes(q, e) =>
        TypeFun(that.pre > q, this.expr.transCompose(e))
    }
  }

  def apply(t: TypeExpr[○, K]): TypeExpr[○, L] =
    TypeFun.toExpr(this ∘ TypeFun.fromExpr(t))

  def compile[==>[_, _], F[_, _], Q](
    fk: F[K, Q],
  )(
    tgt: TypeAlgebra[==>],
    map_● : F[●, tgt.Type],
  )(using
    F: MonoidalObjectMap[F, ×, ○, tgt.<*>, tgt.None],
  ): MappedMorphism[==>, F, K, L] = {
    import tgt.given
    pre.compile(fk)() > expr.compile(tgt, map_●)
  }
}

object TypeFun {
  def apply[K, P, L](r: Routing[K, P], f: TypeExpr[P, L]): TypeFun[K, L] =
    new TypeFun[K, L] {
      override type X = P
      override val pre = r
      override val expr = f
    }

  def unapply[K, L](f: TypeFun[K, L]): (Routing[K, f.X], TypeExpr[f.X, L]) =
    (f.pre, f.expr)

  def fromExpr[K, L](e: TypeExpr[K, L]): TypeFun[K, L] = {
    import e.inKind
    TypeFun(Routing.id[K], e)
  }

  def toExpr[L](f: TypeFun[○, L]): TypeExpr[○, L] =
    Routing.proveId(f.pre).substituteCo[TypeExpr[*, L]](f.expr)

  def unit: TypeFun[○, ●] =
    fromExpr(TypeExpr.unit)

  def int: TypeFun[○, ●] =
    fromExpr(TypeExpr.int)

  def string: TypeFun[○, ●] =
    fromExpr(TypeExpr.string)

  def pair: TypeFun[● × ●, ●] =
    fromExpr(TypeExpr.pair)

  def pair(a: TypeFun[○, ●], b: TypeFun[○, ●]): TypeFun[○, ●] =
    fromExpr(TypeExpr.pair(toExpr(a), toExpr(b)))

  def pair1(a: Type): TypeFun[●, ●] =
    fromExpr(TypeExpr.pair1(a))

  def pair1(a: TypeFun[○, ●]): TypeFun[●, ●] =
    pair1(toExpr(a))

  def sum: TypeFun[● × ●, ●] =
    fromExpr(TypeExpr.sum)

  def sum(a: TypeFun[○, ●], b: TypeFun[○, ●]): TypeFun[○, ●] =
    fromExpr(TypeExpr.sum(toExpr(a), toExpr(b)))

  def sum1(a: Type): TypeFun[●, ●] =
    fromExpr(TypeExpr.sum1(a))

  def sum1(a: TypeFun[○, ●]): TypeFun[●, ●] =
    sum1(toExpr(a))

  def fix(f: TypeFun[●, ●]): TypeFun[○, ●] =
    f match {
      case TypeFun(pre, expr) => fromExpr(TypeExpr.fix(pre, expr))
    }

  def pfix(f: TypeFun[● × ●, ●]): TypeFun[●, ●] =
    f match {
      case TypeFun(pre, expr) => fromExpr(TypeExpr.pfix(pre, expr))
    }

  def composeSnd[K, L, M, N](g: TypeFun[K × M, N], f: TypeFun[L, M])(using
    ProperKind[L],
  ): TypeFun[K × L, N] = {
    def go[X, Y](f1: Routing[L, X], f2: TypeExpr[X, M], g1: Routing[K × M, Y], g2: TypeExpr[Y, N]): TypeFun[K × L, N] = {
      given ProperKind[K] = Kind.fst(g.inKind)
      given OutputKind[M] = f2.outKind

      f2.inKind.properKind match {
        case Left(x_eq_○) =>
          val f20: TypeExpr[○, M] = x_eq_○.substituteCo[TypeExpr[*, M]](f2)
          g1.applyTo(ArgIntro.wrapArgSnd(f20)) match {
            case Routing.ApplyRes(g1, f21) =>
              TypeFun(Routing.elimSnd[K, L] > g1, g2.applyTo(f21))
          }
        case Right(given ProperKind[X]) =>
          g1.applyToTrans(ArgTrans(f2).snd[K]) match {
            case Routing.AppTransRes(g1, f2) =>
              TypeFun(f1.snd[K] > g1, g2.transCompose(f2))
          }
      }
    }

    (f, g) match {
      case (TypeFun(f1, f2), TypeFun(g1, g2)) =>
        go(f1, f2, g1, g2)
    }
  }

  def appFst[K, L, M](f: TypeFun[K × L, M], a: TypeFun[○, K]): TypeFun[L, M] = {
    given OutputKind[K] = a.outKind
    given ProperKind[L] = Kind.snd(f.inKind)

    def go[X](a: TypeExpr[○, K], f1: Routing[K × L, X], f2: TypeExpr[X, M]): TypeFun[L, M] = {
      f1.applyTo(ArgIntro.wrapArgFst(a)) match {
        case Routing.ApplyRes(f0, args) =>
          TypeFun(f0, f2.applyTo(args))
      }
    }

    f match {
      case TypeFun(f1, f2) => go(TypeFun.toExpr(a), f1, f2)
    }
  }

  def scalaTypeParam[T](filename: String, line: Int, name: String): TypeFun[○, ●] =
    fromExpr(TypeExpr.scalaTypeParam(filename, line, name))
}
