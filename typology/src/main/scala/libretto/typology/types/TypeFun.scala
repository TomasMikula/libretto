package libretto.typology.types

import libretto.lambda.{MappedMorphism, MonoidalObjectMap}
import libretto.typology.kinds._
import libretto.lambda.SymmetricMonoidalCategory

sealed trait TypeFun[TC[_, _], K, L] {
  type X
  type Expr[k, l] = TypeExpr[TC, k, l]

  val pre: Routing[K, X]
  val expr: Expr[X, L]

  given inKind: Kinds[K] = pre.inKind
  given outKind: Kind[L] = expr.outKind

  def ∘[J](that: TypeFun[TC, J, K]): TypeFun[TC, J, L] = {
    import that.pre.outKind
    import that.expr.outKind

    this.pre.applyTo[Expr, that.X](PartialArgs(that.expr)) match {
      case Routing.AppRes.Impl(q, e) =>
        TypeFun(that.pre > q, this.expr.applyTo(e))
    }
  }

  def apply(t: Expr[○, K]): Expr[○, L] =
    TypeFun.toExpr(this ∘ TypeFun.fromExpr(t))

  def applyTo[J](args: PartialArgs[Expr, J, K]): TypeFun[TC, J, L] =
    this.pre.applyTo(args) match
      case Routing.AppRes.Impl(p, a) =>
        TypeFun(p, this.expr.applyTo(a))

  def translate[TC1[_, _]](f: [k, l] => TC[k, l] => TC1[k, l]): TypeFun[TC1, K, L] =
    TypeFun(pre, expr.translate(f))

  def compile[==>[_, _], <*>[_, _], One, F[_, _], Q](
    fk: F[K, Q],
    compilePrimitive: [k, l, q] => (F[k, q], TC[k, l]) => MappedMorphism[==>, F, k, l],
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
}

object TypeFun {
  def apply[TC[_, _], K, P, L](r: Routing[K, P], f: TypeExpr[TC, P, L]): TypeFun[TC, K, L] =
    new TypeFun[TC, K, L] {
      override type X = P
      override val pre = r
      override val expr = f
    }

  def apply[TC[_, _], K, P, L](r: Routing[K, P], f: TypeFun[TC, P, L]): TypeFun[TC, K, L] =
    TypeFun(r > f.pre, f.expr)

  def unapply[TC[_, _], K, L](f: TypeFun[TC, K, L]): (Routing[K, f.X], TypeExpr[TC, f.X, L]) =
    (f.pre, f.expr)

  def fromExpr[TC[_, _], K, L](e: TypeExpr[TC, K, L]): TypeFun[TC, K, L] = {
    import e.inKind
    TypeFun(Routing.id[K], e)
  }

  def toExpr[TC[_, _], L](f: TypeFun[TC, ○, L]): TypeExpr[TC, ○, L] =
    Routing.proveId(f.pre).substituteCo[TypeExpr[TC, _, L]](f.expr)

  def composeSnd[TC[_, _], K, L, M, N](g: TypeFun[TC, K × M, N], f: TypeFun[TC, L, M])(using
    KindN[L],
  ): TypeFun[TC, K × L, N] = {
    type Expr[k, l] = TypeExpr[TC, k, l]

    def go[X, Y](
      f1: Routing[L, X],
      f2: Expr[X, M],
      g1: Routing[K × M, Y],
      g2: Expr[Y, N],
    ): TypeFun[TC, K × L, N] = {
      given KindN[K] = Kinds.fstOf(g.inKind)
      given Kind[M] = f2.outKind

      f2.inKind.nonEmpty match {
        case Left(x_eq_○) =>
          val f20: Expr[○, M] = x_eq_○.substituteCo[Expr[_, M]](f2)
          g1.applyTo(PartialArgs.introSnd(PartialArgs(f20))) match {
            case Routing.AppRes.Impl(g1, f21) =>
              TypeFun(Routing.elimSnd[K, L] > g1, g2.applyTo(f21))
          }
        case Right(given KindN[X]) =>
          g1.applyTo(PartialArgs(f2).inSnd[K]) match {
            case Routing.AppRes.Impl(g1, f2) =>
              TypeFun(f1.inSnd[K] > g1, g2.applyTo(f2))
          }
      }
    }

    (f, g) match {
      case (TypeFun(f1, f2), TypeFun(g1, g2)) =>
        go(f1, f2, g1, g2)
    }
  }

  def appFst[TC[_, _], K, L, M](f: TypeFun[TC, K × L, M], a: TypeFun[TC, ○, K]): TypeFun[TC, L, M] = {
    given Kind[K] = a.outKind
    given KindN[L] = Kinds.sndOf(f.inKind)

    type Expr[k, l] = TypeExpr[TC, k, l]

    def go[X](a: Expr[○, K], f1: Routing[K × L, X], f2: Expr[X, M]): TypeFun[TC, L, M] = {
      f1.applyTo(PartialArgs.introFst(PartialArgs(a))) match {
        case Routing.AppRes.Impl(f0, args) =>
          TypeFun(f0, f2.applyTo(args))
      }
    }

    f match {
      case TypeFun(f1, f2) => go(TypeFun.toExpr(a), f1, f2)
    }
  }
}
