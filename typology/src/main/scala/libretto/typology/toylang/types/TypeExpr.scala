package libretto.typology.toylang.types

import libretto.lambda.{MappedMorphism, MonoidalObjectMap, SemigroupalCategory}
import libretto.lambda.util.{Exists, Monad, SourcePos}
import libretto.lambda.util.Monad.syntax._
import libretto.typology.kinds._
import libretto.typology.toylang.types.generic.{TypeExpr => gte}

case class TypeExpr[V, K, L](value: generic.TypeExpr[V, TypeExpr[V, _, _], K, L]) {
  given inKind: Kind[K] = value.inKind
  given outKind: OutputKind[L] = value.outKind

  def foldM[F[_, _], M[_]: Monad](f: [k, l] => generic.TypeExpr[V, F, k, l] => M[F[k, l]]): M[F[K, L]] = {
    value
      .translateM[F, M]([x, y] => (te: TypeExpr[V, x, y]) => te.foldM[F, M](f))
      .flatMap(f(_))
  }

  def ∘[J](that: TypeExpr[V, J, K]): TypeExpr[V, J, L] =
    that.inKind.properKind match {
      case Left(j_eq_○) =>
        j_eq_○.substituteContra[TypeExpr[V, *, L]](applyTo(j_eq_○.substituteCo[TypeExpr[V, *, K]](that)))
      case Right(j) =>
        composeProper(that)(using j)
    }

  def composeProper[J](that: TypeExpr[V, J, K])(using j: ProperKind[J]): TypeExpr[V, J, L] = {
    import generic.{TypeExpr => gt}

    TypeExpr(
      (that.value, this.value) match {
        case (f, gt.AppFst(g, b1)) =>
          gt.AppCompose(g, b1, TypeExpr(f))
        case (a, b) =>
          throw new NotImplementedError(s"$b ∘ $a (${summon[SourcePos]})")
      }
    )
  }

  def applyTo(that: TypeExpr[V, ○, K]): TypeExpr[V, ○, L] = {
    import that.outKind
    applyTo(ArgIntro.wrapArg(that))
  }

  def applyTo[J](that: ArgIntro[TypeExpr[V, ○, *], J, K]): TypeExpr[V, J, L] =
    TypeExpr(
      this.value.transApply[TypeExpr[V, _, _], J](
        that,
        [k, l] => (te: TypeExpr[V, k, l]) => te,
        [j, k, l] => (te: TypeExpr[V, k, l], a: ArgIntro[TypeExpr[V, ○, *], j, k]) => te.applyTo(a),
      )
    )

  def transCompose[J](that: ArgTrans[TypeExpr[V, _, _], J, K]): TypeExpr[V, J, L] =
    TypeExpr(
      this.value.transCompose[TypeExpr[V, _, _], J](
        that,
        [k, l] => (te: TypeExpr[V, k, l]) => te,
        [j, k, l] => (te: TypeExpr[V, k, l], a: ArgTrans[TypeExpr[V, _, _], j, k]) => te.transCompose(a),
      )
    )

  def >[M](that: TypeExpr[V, L, M]): TypeExpr[V, K, M] =
    that ∘ this

  override def toString: String =
    value.toString

  def compile[==>[_, _], F[_, _]](
    tgt: TypeAlgebra[V, ==>],
    map_● : F[●, tgt.Type],
  )(using
    F: MonoidalObjectMap[F, ×, ○, tgt.<*>, tgt.None],
  ): MappedMorphism[==>, F, K, L] = {
    import tgt.given
    this.value match
      case gte.UnitType() =>
        MappedMorphism(F.unit, tgt.unit, map_●)
      case gte.IntType() =>
        MappedMorphism(F.unit, tgt.int, map_●)
      case gte.StringType() =>
        MappedMorphism(F.unit, tgt.string, map_●)
      case gte.Pair() =>
        MappedMorphism(F.pair(map_●, map_●), tgt.pair, map_●)
      case gte.Sum() =>
        MappedMorphism(F.pair(map_●, map_●), tgt.sum, map_●)
      case gte.RecCall() =>
        MappedMorphism(F.pair(map_●, map_●), tgt.recCall, map_●)
      case gte.Fix(f, g) =>
        MappedMorphism(F.unit, tgt.fix(TypeFun(f, g)), map_●)
      case gte.PFix(f, g) =>
        throw NotImplementedError(s"PFix($f, $g) at ${summon[SourcePos]}")
      case gte.AbstractType(label) =>
        MappedMorphism(F.unit, tgt.abstractTypeName(label), map_●)
      case gte.ScalaTypeParams(values) =>
        throw NotImplementedError(s"ScalaTypeParams($values) at ${summon[SourcePos]}")
      case gte.BiApp(op, a, b) =>
        MappedMorphism(
          F.unit,
          tgt.category.introFst,
          F.pair(F.unit, F.unit),
        ) >
        MappedMorphism.par(
          a.compile(tgt, map_●),
          b.compile(tgt, map_●),
        ) >
        TypeExpr(op).compile(tgt, map_●)
      case gte.AppFst(op, a) =>
        val op1 = TypeExpr(op).compile(tgt, map_●)
        val a1  = a.compile(tgt, map_●)
        MappedMorphism.composeIntroFst(
          MappedMorphism.composeFst(op1, a1),
        )
      case gte.AppSnd(op, b) =>
        val op1 = TypeExpr(op).compile(tgt, map_●)
        val b1  = b.compile(tgt, map_●)
        MappedMorphism.composeIntroSnd(
          MappedMorphism.composeSnd(op1, b1),
        )
      case gte.ComposeSnd(op, g) =>
        val op1 = TypeExpr(op).compile(tgt, map_●)
        val g1  = g.compile(tgt, map_●)
        MappedMorphism.composeSnd(op1, g1)
      case gte.AppCompose(op, a, g) =>
        val op1 = TypeExpr(op).compile(tgt, map_●)
        val a1  = a.compile(tgt, map_●)
        val g1  = g.compile(tgt, map_●)
        MappedMorphism.composeIntroFst(
          MappedMorphism.par(a1, g1) > op1
        )
      case gte.TypeMismatch(a, b) =>
        throw NotImplementedError(s"TypeMismatch($a, $b) at ${summon[SourcePos]}")
  }

  def vmap[W](f: V => W): TypeExpr[W, K, L] =
    TypeExpr(
      value
        .vmap(f)
        .translate[TypeExpr[W, _, _]]([k, l] => (e: TypeExpr[V, k, l]) => e.vmap(f))
    )
}

object TypeExpr {
  def unit[V]: TypeExpr[V, ○, ●] =
    TypeExpr(generic.TypeExpr.UnitType())

  def int[V]: TypeExpr[V, ○, ●] =
    TypeExpr(generic.TypeExpr.IntType())

  def string[V]: TypeExpr[V, ○, ●] =
    TypeExpr(generic.TypeExpr.StringType())

  def abstractType[V](label: V): TypeExpr[V, ○, ●] =
    TypeExpr(generic.TypeExpr.abstractType(label))

  def appFst[V, K1, K2, L](
    op: generic.TypeExpr.BinaryOperator[V, ?, K1, K2, L],
    arg1: TypeExpr[V, ○, K1],
  ): TypeExpr[V, K2, L] =
    TypeExpr(generic.TypeExpr.AppFst(op.cast[TypeExpr[V, _, _]], arg1))

  def appCompose[V, K: ProperKind, L1, L2, M](
    op: generic.TypeExpr.BinaryOperator[V, ?, L1, L2, M],
    arg1: TypeExpr[V, ○, L1],
    arg2: TypeExpr[V, K, L2],
  ): TypeExpr[V, K, M] = {
    import arg2.{given Kind[K]}
    TypeExpr(generic.TypeExpr.AppCompose(op.cast[TypeExpr[V, _, _]], arg1, arg2))
  }

  def biApp[V, K1, K2, L](
    op: generic.TypeExpr.BinaryOperator[V, ?, K1, K2, L],
    arg1: TypeExpr[V, ○, K1],
    arg2: TypeExpr[V, ○, K2],
  ): TypeExpr[V, ○, L] =
    TypeExpr(generic.TypeExpr.BiApp(op.cast[TypeExpr[V, _, _]], arg1, arg2))

  def composeSnd[V, L1, K2: ProperKind, L2, M](
    op: TypeExpr[V, L1 × L2, M],
    arg2: TypeExpr[V, K2, L2],
  ): TypeExpr[V, L1 × K2, M] = {
    import arg2.outKind
    given ProperKind[L1] = Kind.fst(op.inKind)

    op.transCompose(ArgTrans.snd(ArgTrans.wrap(arg2)))
  }

  def pair[V]: TypeExpr[V, ● × ●, ●] =
    TypeExpr(generic.TypeExpr.Pair())

  def pair[V](a: TypeExpr[V, ○, ●], b: TypeExpr[V, ○, ●]): TypeExpr[V, ○, ●] =
    TypeExpr(generic.TypeExpr.pair(a, b))

  def pair1[V](a: TypeExpr[V, ○, ●]): TypeExpr[V, ●, ●] =
    TypeExpr(generic.TypeExpr.pair1(a))

  def sum[V]: TypeExpr[V, ● × ●, ●] =
    TypeExpr(generic.TypeExpr.Sum())

  def sum[V](a: TypeExpr[V, ○, ●], b: TypeExpr[V, ○, ●]): TypeExpr[V, ○, ●] =
    TypeExpr(generic.TypeExpr.sum(a, b))

  def sum1[V](a: TypeExpr[V, ○, ●]): TypeExpr[V, ●, ●] =
    TypeExpr(generic.TypeExpr.sum1(a))

  def fix[V, K](f: Routing[●, K], g: TypeExpr[V, K, ●]): TypeExpr[V, ○, ●] =
    TypeExpr(generic.TypeExpr.Fix(f, g))

  def pfix[V, K: ProperKind, X](f: Routing[K × ●, X], g: TypeExpr[V, X, ●]): TypeExpr[V, K, ●] =
    TypeExpr(generic.TypeExpr.PFix(f, g))

  def scalaTypeParam[V, T](filename: String, line: Int, name: String): TypeExpr[V, ○, ●] =
    TypeExpr(generic.TypeExpr.ScalaTypeParams.one(filename, line, name))

  def typeMismatch[V, K: Kind, L: OutputKind](a: TypeExpr[V, K, L], b: TypeExpr[V, K, L]): TypeExpr[V, K, L] =
    TypeExpr(generic.TypeExpr.TypeMismatch(a, b))
}
