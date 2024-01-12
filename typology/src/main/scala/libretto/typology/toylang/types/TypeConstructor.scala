package libretto.typology.toylang.types

import libretto.lambda.{MappedMorphism,  MonoidalObjectMap, UnhandledCase}
import libretto.typology.kinds._

sealed trait TypeConstructor[V, K, L](using
  val inKind: Kind[K],
  val outKind: OutputKind[L],
) {
  import TypeConstructor.*

  def vmap[W](f: V => W): TypeConstructor[W, K, L] =
    val go = TypeConstructor.vmap(f)
    this match {
      case AbstractType(label) => AbstractType(f(label))
      case Fix(g, h)           => Fix(g, h.translate(go))
      case x @ PFix(g, h)      => import x.given; PFix(g, h.translate(go))
      case UnitType()          => UnitType()
      case IntType()           => IntType()
      case StringType()        => StringType()
      case Pair()              => Pair()
      case Sum()               => Sum()
      case RecCall()           => RecCall()
      case TypeMismatch(a, b)  => TypeMismatch(a.translate(go), b.translate(go))
      case ForbiddenSelfRef(v) => ForbiddenSelfRef(f(v))
    }

  def compile[==>[_, _], F[_, _], Q](
    tgt: TypeAlgebra[V, ==>],
    fk: F[K, Q],
    map_● : F[●, tgt.Type],
  )(using
    F: MonoidalObjectMap[F, ×, ○, tgt.<*>, tgt.None],
  ): MappedMorphism[==>, F, K, L] =
    this match {
      case UnitType() =>
        MappedMorphism(F.unit, tgt.unit, map_●)
      case IntType() =>
        MappedMorphism(F.unit, tgt.int, map_●)
      case StringType() =>
        MappedMorphism(F.unit, tgt.string, map_●)
      case Pair() =>
        MappedMorphism(F.pair(map_●, map_●), tgt.pair, map_●)
      case Sum() =>
        MappedMorphism(F.pair(map_●, map_●), tgt.sum, map_●)
      case RecCall() =>
        MappedMorphism(F.pair(map_●, map_●), tgt.recCall, map_●)
      case Fix(f, g) =>
        MappedMorphism(F.unit, tgt.fix(TypeFun(f, g)), map_●)
      case PFix(f, g) =>
        MappedMorphism(map_●, tgt.pfix(TypeFun(f, g)), map_●)
      case AbstractType(label) =>
        MappedMorphism(F.unit, tgt.abstractTypeName(label), map_●)
      case TypeMismatch(a, b) =>
        UnhandledCase.raise(s"TypeMismatch($a, $b)")
      case ForbiddenSelfRef(v) =>
        UnhandledCase.raise(s"ForbiddenSelfReference($v)")
    }
}

object TypeConstructor {
  case class AbstractType[V](label: V) extends TypeConstructor[V, ○, ●]

  case class UnitType[V]() extends TypeConstructor[V, ○, ●]
  case class IntType[V]() extends TypeConstructor[V, ○, ●]
  case class StringType[V]() extends TypeConstructor[V, ○, ●]

  case class Pair[V]() extends TypeConstructor[V, ● × ●, ●]
  case class Sum[V]() extends TypeConstructor[V, ● × ●, ●]
  case class RecCall[V]() extends TypeConstructor[V, ● × ●, ●]

  case class Fix[V, K](
    f: Routing[●, K],
    g: TypeExpr[TypeConstructor[V, _, _], K, ●],
  ) extends TypeConstructor[V, ○, ●]

  // TODO: Make the representation normalized (part of initial routing may possibly be factored out)
  case class PFix[V, X](
    f: Routing[● × ●, X],
    g: TypeExpr[TypeConstructor[V, _, _], X, ●],
  ) extends TypeConstructor[V, ●, ●]

  case class TypeMismatch[V, K: Kind, L: OutputKind](
    a: TypeExpr[TypeConstructor[V, _, _], K, L],
    b: TypeExpr[TypeConstructor[V, _, _], K, L],
  ) extends TypeConstructor[V, K, L]

  case class ForbiddenSelfRef[V, K: Kind, L: OutputKind](
    v: V,
  ) extends TypeConstructor[V, K, L]

  def vmap[V, W](
    f: V => W
  ): [k, l] => TypeConstructor[V, k, l] => TypeConstructor[W, k, l] =
    [k, l] => (tc: TypeConstructor[V, k, l]) => tc.vmap(f)
}
