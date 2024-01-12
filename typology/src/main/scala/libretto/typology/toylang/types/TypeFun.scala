package libretto.typology.toylang.types

import libretto.lambda.{MappedMorphism, MonoidalObjectMap}
import libretto.typology.kinds._
import libretto.lambda.SymmetricMonoidalCategory

sealed trait TypeFun[V, K, L] {
  type X
  type Expr[k, l] = TypeExpr[TypeConstructor[V, _, _], k, l]

  val pre: Routing[K, X]
  val expr: Expr[X, L]

  given inKind: Kind[K] = pre.inKind
  given outKind: OutputKind[L] = expr.outKind

  def ∘[J](that: TypeFun[V, J, K]): TypeFun[V, J, L] = {
    import that.pre.outKind
    import that.expr.outKind

    this.pre.applyTo[Expr, that.X](PartialArgs(that.expr)) match {
      case Routing.AppTransRes.Impl(q, e) =>
        TypeFun(that.pre > q, this.expr.applyTo(e))
    }
  }

  def apply(t: Expr[○, K]): Expr[○, L] =
    TypeFun.toExpr(this ∘ TypeFun.fromExpr(t))

  def compile[==>[_, _], <*>[_, _], One, F[_, _], Q](
    fk: F[K, Q],
    compilePrimitive: [k, l, q] => (F[k, q], TypeConstructor[V, k, l]) => MappedMorphism[==>, F, k, l],
    dupTypes: [k, q] => F[k, q] => (q ==> q <*> q),
  )(using
    tgt: SymmetricMonoidalCategory[==>, <*>, One],
    F: MonoidalObjectMap[F, ×, ○, <*>, One],
  ): MappedMorphism[==>, F, K, L] = {
    val pre1: MappedMorphism[==>, F, K, X] =
      pre.compile[==>, F, <*>, One, Q](fk)(dupTypes)
    val expr1: MappedMorphism[==>, F, X, L] =
      expr.compile(pre1.tgtMap, compilePrimitive)
    pre1 > expr1
  }

  def vmap[W](f: V => W): TypeFun[W, K, L] =
    TypeFun(pre, expr.translate(TypeConstructor.vmap(f)))
}

object TypeFun {
  def apply[V, K, P, L](r: Routing[K, P], f: TypeExpr[TypeConstructor[V, _, _], P, L]): TypeFun[V, K, L] =
    new TypeFun[V, K, L] {
      override type X = P
      override val pre = r
      override val expr = f
    }

  def apply[V, K, P, L](r: Routing[K, P], f: TypeFun[V, P, L]): TypeFun[V, K, L] =
    TypeFun(r > f.pre, f.expr)

  def unapply[V, K, L](f: TypeFun[V, K, L]): (Routing[K, f.X], TypeExpr[TypeConstructor[V, _, _], f.X, L]) =
    (f.pre, f.expr)

  def fromExpr[V, K, L](e: TypeExpr[TypeConstructor[V, _, _], K, L]): TypeFun[V, K, L] = {
    import e.inKind
    TypeFun(Routing.id[K], e)
  }

  def toExpr[V, L](f: TypeFun[V, ○, L]): TypeExpr[TypeConstructor[V, _, _], ○, L] =
    Routing.proveId(f.pre).substituteCo[TypeExpr[TypeConstructor[V, _, _], _, L]](f.expr)

  def unit[V]: TypeFun[V, ○, ●] =
    fromExpr(Type.unit)

  def int[V]: TypeFun[V, ○, ●] =
    fromExpr(Type.int)

  def string[V]: TypeFun[V, ○, ●] =
    fromExpr(Type.string)

  def pair[V]: TypeFun[V, ● × ●, ●] =
    fromExpr(Type.pair)

  def pair[V](a: TypeFun[V, ○, ●], b: TypeFun[V, ○, ●]): TypeFun[V, ○, ●] =
    fromExpr(Type.pair(toExpr(a), toExpr(b)))

  def pair1[V](a: Type[V]): TypeFun[V, ●, ●] =
    fromExpr(TypeExpr.App(TypeConstructor.Pair(), PartialArgs.introFst(PartialArgs(a))))

  def pair1[V](a: TypeFun[V, ○, ●]): TypeFun[V, ●, ●] =
    pair1(toExpr(a))

  def pair2[V](b: Type[V]): TypeFun[V, ●, ●] =
    fromExpr(TypeExpr.App(TypeConstructor.Pair(), PartialArgs.introSnd(PartialArgs(b))))

  def pair2[V](b: TypeFun[V, ○, ●]): TypeFun[V, ●, ●] =
    pair2(toExpr(b))

  def sum[V]: TypeFun[V, ● × ●, ●] =
    fromExpr(TypeExpr.Primitive(TypeConstructor.Sum()))

  def sum[V](a: TypeFun[V, ○, ●], b: TypeFun[V, ○, ●]): TypeFun[V, ○, ●] =
    fromExpr(Type.sum(toExpr(a), toExpr(b)))

  def sum1[V](a: Type[V]): TypeFun[V, ●, ●] =
    fromExpr(TypeExpr.App(TypeConstructor.Sum(), PartialArgs.introFst(PartialArgs(a))))

  def sum1[V](a: TypeFun[V, ○, ●]): TypeFun[V, ●, ●] =
    sum1(toExpr(a))

  def sum2[V](b: Type[V]): TypeFun[V, ●, ●] =
    fromExpr(TypeExpr.App(TypeConstructor.Sum(), PartialArgs.introSnd(PartialArgs(b))))

  def fix[V](f: TypeFun[V, ●, ●]): TypeFun[V, ○, ●] =
    fromExpr(Type.fix(f))

  def pfix[V](f: TypeFun[V, ● × ●, ●]): TypeFun[V, ●, ●] =
    f match {
      case TypeFun(pre, expr) => fromExpr(TypeExpr.Primitive(TypeConstructor.PFix(pre, expr)))
    }

  def composeSnd[V, K, L, M, N](g: TypeFun[V, K × M, N], f: TypeFun[V, L, M])(using
    ProperKind[L],
  ): TypeFun[V, K × L, N] = {
    def go[X, Y](
      f1: Routing[L, X],
      f2: TypeExpr[TypeConstructor[V, _, _], X, M],
      g1: Routing[K × M, Y],
      g2: TypeExpr[TypeConstructor[V, _, _], Y, N],
    ): TypeFun[V, K × L, N] = {
      given ProperKind[K] = Kind.fst(g.inKind)
      given OutputKind[M] = f2.outKind

      type Expr[k, l] = TypeExpr[TypeConstructor[V, _, _], k, l]

      f2.inKind.properKind match {
        case Left(x_eq_○) =>
          val f20: Expr[○, M] = x_eq_○.substituteCo[Expr[_, M]](f2)
          g1.applyTo(PartialArgs.introSnd(PartialArgs(f20))) match {
            case Routing.AppTransRes.Impl(g1, f21) =>
              TypeFun(Routing.elimSnd[K, L] > g1, g2.applyTo(f21))
          }
        case Right(given ProperKind[X]) =>
          g1.applyTo(PartialArgs(f2).inSnd[K]) match {
            case Routing.AppTransRes.Impl(g1, f2) =>
              TypeFun(f1.inSnd[K] > g1, g2.applyTo(f2))
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

    type Expr[k, l] = TypeExpr[TypeConstructor[V, _, _], k, l]

    def go[X](a: Expr[○, K], f1: Routing[K × L, X], f2: Expr[X, M]): TypeFun[V, L, M] = {
      f1.applyTo(PartialArgs.introFst(PartialArgs(a))) match {
        case Routing.AppTransRes.Impl(f0, args) =>
          TypeFun(f0, f2.applyTo(args))
      }
    }

    f match {
      case TypeFun(f1, f2) => go(TypeFun.toExpr(a), f1, f2)
    }
  }

  def abstractType[V](name: V): TypeFun[V, ○, ●] =
    fromExpr(TypeExpr.Primitive(TypeConstructor.AbstractType(name)))
}
