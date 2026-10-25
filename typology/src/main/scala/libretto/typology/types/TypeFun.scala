package libretto.typology.types

import libretto.lambda.{MappedMorphism, MonoidalObjectMap}
import libretto.lambda.util.Exists
import libretto.lambda.util.Exists.Indeed
import libretto.typology.kinds.*
import libretto.lambda.SymmetricMonoidalCategory

sealed trait TypeFun[TC[_, _], K, L] {
  type Expr[k, l] = TypeExpr[TC, k, l]

  given inKind: Kinds[K]
  given outKind: Kind[L]

  def ∘[J](that: TypeFun[TC, J, K]): TypeFun[TC, J, L]

  def ∘[J](that: Routing[J, K]): TypeFun[TC, J, L]

  def apply(t: Expr[○, K]): Expr[○, L] =
    TypeFun.toExpr(this ∘ TypeFun.fromExpr(t))

  def applyTo[J](args: PartialArgs[Expr, J, K]): TypeFun[TC, J, L]

  def translate[TC1[_, _]](f: [k, l] => TC[k, l] => TC1[k, l]): TypeFun[TC1, K, L]

  def compile[==>[_, _], <*>[_, _], One, F[_, _], Q](
    fk: F[K, Q],
    compilePrimitive: [k, l, q] => (F[k, q], TC[k, l]) => MappedMorphism[==>, F, k, l],
    dupTypes: [k, q] => F[k, q] => (q ==> q <*> q),
  )(using
    tgt: SymmetricMonoidalCategory[==>, <*>, One],
    F: MonoidalObjectMap[F, ×, ○, <*>, One],
  ): MappedMorphism[==>, F, K, L]

  protected def thenRoutingOnly[M](that: TypeFun.RoutingOnly[TC, L, M]): TypeFun[TC, K, M]
  protected def thenProper[Q, M](that: TypeFun.Proper[TC, L, Q, M]): TypeFun[TC, K, M]
  protected def decompose: Exists[[X] =>> (Routing[K, X], PartialArgs[Expr, X, L])]
}

object TypeFun {
  case class RoutingOnly[TC[_, _], K, L](
    routing: Routing[K, L],
    override val outKind: Kind[L],
  ) extends TypeFun[TC, K, L] {
    override def inKind: Kinds[K] = routing.inKind

    override def ∘[J](that: TypeFun[TC, J, K]): TypeFun[TC, J, L] =
      that.thenRoutingOnly(this)

    override def ∘[J](that: Routing[J, K]): TypeFun[TC, J, L] =
      RoutingOnly(that > routing, outKind)

    override def applyTo[J](args: PartialArgs[Expr, J, K]): TypeFun[TC, J, L] =
      this.routing.applyTo(args) match
        case Routing.AppRes.Impl(p, a) =>
          TypeFun(p, a)(using outKind)

    override def translate[TC1[_,_]](f: [k, l] => TC[k, l] => TC1[k, l]): TypeFun[TC1, K, L] =
      RoutingOnly(routing, outKind)

    override def compile[==>[_, _], <*>[_, _], One, F[_, _], Q](
      fk: F[K, Q],
      compilePrimitive: [k, l, q] => (F[k, q], TC[k, l]) => MappedMorphism[==>, F, k, l],
      dupTypes: [k, q] => F[k, q] => (q ==> q <*> q),
    )(using
      tgt: SymmetricMonoidalCategory[==>, <*>, One],
      F: MonoidalObjectMap[F, ×, ○, <*>, One],
    ): MappedMorphism[==>, F, K, L] =
      routing.compile[==>, F, <*>, One, Q](fk)(dupTypes)

    override protected def thenRoutingOnly[M](that: RoutingOnly[TC, L, M]): TypeFun[TC, K, M] =
      that ∘ routing

    override protected def thenProper[Q, M](that: Proper[TC, L, Q, M]): TypeFun[TC, K, M] =
      that ∘ routing

    override protected def decompose: Exists[[X] =>> (Routing[K, X], PartialArgs[Expr, X, L])] =
      Indeed((routing, PartialArgs.Id()(using KindN(outKind))))
  }

  case class Proper[TC[_, _], K, P, L](
    pre: Routing[K, P],
    expr: TypeExpr[TC, P, L],
  ) extends TypeFun[TC, K, L] {

    override given inKind: Kinds[K] = pre.inKind
    override given outKind: Kind[L] = expr.outKind

    override def ∘[J](that: TypeFun[TC, J, K]): TypeFun[TC, J, L] =
      that.thenProper(this)

    override def ∘[J](that: Routing[J, K]): TypeFun[TC, J, L] =
      Proper(that > pre, expr)

    override def applyTo[J](args: PartialArgs[Expr, J, K]): TypeFun[TC, J, L] =
      this.pre.applyTo(args) match
        case Routing.AppRes.Impl(p, a) =>
          Proper(p, this.expr.applyTo(a))

    override def translate[TC1[_, _]](f: [k, l] => TC[k, l] => TC1[k, l]): TypeFun[TC1, K, L] =
      Proper(pre, expr.translate(f))

    override def compile[==>[_, _], <*>[_, _], One, F[_, _], Q](
      fk: F[K, Q],
      compilePrimitive: [k, l, q] => (F[k, q], TC[k, l]) => MappedMorphism[==>, F, k, l],
      dupTypes: [k, q] => F[k, q] => (q ==> q <*> q),
    )(using
      tgt: SymmetricMonoidalCategory[==>, <*>, One],
      F: MonoidalObjectMap[F, ×, ○, <*>, One],
    ): MappedMorphism[==>, F, K, L] = {
      val pre1: MappedMorphism[==>, F, K, P] =
        pre.compile[==>, F, <*>, One, Q](fk)(dupTypes)
      val expr1: MappedMorphism[==>, F, P, L] =
        expr.compile(pre1.tgtMap, compilePrimitive)
      pre1 > expr1
    }

    override protected def thenRoutingOnly[M](that: RoutingOnly[TC, L, M]): TypeFun[TC, K, M] = {
      import pre.outKind
      that.routing.applyTo[Expr, P](PartialArgs(expr)) match
        case Routing.AppRes.Impl(q, e) =>
          TypeFun(pre > q, e)(using that.outKind)
    }

    override protected def thenProper[Q, M](that: TypeFun.Proper[TC, L, Q, M]): TypeFun[TC, K, M] = {
      import pre.outKind
      import expr.outKind

      that.pre.applyTo[Expr, P](PartialArgs(expr)) match {
        case Routing.AppRes.Impl(q, e) =>
          Proper(pre > q, that.expr.applyTo(e))
      }
    }

    override protected def decompose: Exists[[X] =>> (Routing[K, X], PartialArgs[Expr, X, L])] =
      Indeed((pre, PartialArgs(expr)(using expr.inKind)))

  }

  def apply[TC[_, _], K, P, L](r: Routing[K, P], f: TypeExpr[TC, P, L]): TypeFun[TC, K, L] =
    Proper(r, f)

  def apply[TC[_, _], K, P, L](r: Routing[K, P], f: PartialArgs[TypeExpr[TC, _, _], P, L])(using Kind[L]): TypeFun[TC, K, L] =
    f.extractSingle match
      case Left(ev) => RoutingOnly(r.to(using ev), Kind[L])
      case Right(f) => Proper(r, f)

  def fromExpr[TC[_, _], K, L](e: TypeExpr[TC, K, L]): TypeFun[TC, K, L] = {
    import e.inKind
    TypeFun(Routing.id[K], e)
  }

  def toExpr[TC[_, _], L](f: TypeFun[TC, ○, L]): TypeExpr[TC, ○, L] =
    f match
      case Proper(pre, expr) =>
        Routing.proveId(pre).substituteCo[TypeExpr[TC, _, L]](expr)
      case RoutingOnly(routing, outKind) =>
        Kind.cannotBeUnit(Routing.proveId(routing).substituteCo(outKind))

  def composeSnd[TC[_, _], K, L, M, N](g: TypeFun[TC, K × M, N], f: TypeFun[TC, L, M])(using
    KindN[L],
  ): TypeFun[TC, K × L, N] = {
    type Expr[k, l] = TypeExpr[TC, k, l]

    def go[X, Y](
      f1: Routing[L, X],
      f2: PartialArgs[Expr, X, M],
      g1: Routing[K × M, Y],
      g2: PartialArgs[Expr, Y, N],
    )(using
      Kind[M],
      Kind[N],
    ): TypeFun[TC, K × L, N] = {
      given KindN[K] = Kinds.fstOf(g.inKind)

      f2.inKind.nonEmpty match {
        case Left(x_eq_○) =>
          val f20: PartialArgs[Expr, ○, M] = x_eq_○.substituteCo[PartialArgs[Expr, _, M]](f2)
          g1.applyTo(PartialArgs.introSnd(f20)) match {
            case Routing.AppRes.Impl(g1, f21) =>
              TypeFun(Routing.elimSnd[K, L] > g1, (f21 > g2)(TypeExpr.absorbArgs[TC]))(using Kind[N])
          }
        case Right(given KindN[X]) =>
          g1.applyTo(f2.inSnd[K]) match {
            case Routing.AppRes.Impl(g1, f2) =>
              TypeFun(f1.inSnd[K] > g1, (f2 > g2)(TypeExpr.absorbArgs[TC]))
          }
      }
    }

    (f.decompose, g.decompose) match {
      case (Indeed((f1, f2)), Indeed((g1, g2))) =>
        go(f1, f2, g1, g2)(using f.outKind, g.outKind)
    }
  }

  def appFst[TC[_, _], K, L, M](f: TypeFun[TC, K × L, M], a: TypeFun[TC, ○, K]): TypeFun[TC, L, M] = {
    given Kind[K] = a.outKind
    given KindN[L] = Kinds.sndOf(f.inKind)

    type Expr[k, l] = TypeExpr[TC, k, l]

    def goRouting(a: Expr[○, K], f1: Routing[K × L, M], m: Kind[M]): TypeFun[TC, L, M] = {
      f1.applyTo(PartialArgs.introFst(PartialArgs(a))) match {
        case Routing.AppRes.Impl(f0, args) =>
          TypeFun(f0, args)(using m)
      }
    }

    def go[X](a: Expr[○, K], f1: Routing[K × L, X], f2: Expr[X, M]): TypeFun[TC, L, M] = {
      f1.applyTo(PartialArgs.introFst(PartialArgs(a))) match {
        case Routing.AppRes.Impl(f0, args) =>
          TypeFun(f0, f2.applyTo(args))
      }
    }

    val a0 = TypeFun.toExpr(a)

    f match {
      case RoutingOnly(f1, m) => goRouting(a0, f1, m)
      case Proper(f1, f2) => go(a0, f1, f2)
    }
  }
}
