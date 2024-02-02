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
    m: Multiplier[×, ●, K],
    g: OpenTypeExpr[TypeConstructor[V, _, _], K, ●],
  ) extends TypeConstructor[V, ○, ●] {
    override def vmap[W](f: V => W): Fix[W, K] =
      Fix(m, g.translate(TypeConstructor.vmap(f)))
  }

  case class PFix[V, P, X](
    m: Multiplier[×, ●, X],
    g: OpenTypeExpr.LTrimmed[TypeConstructor[V, _, _], P, X, ●],
  ) extends TypeConstructor[V, P, ●](using g.inKind1.kind) {
    override def vmap[W](f: V => W): PFix[W, P, X] =
      PFix(m, g.translate(TypeConstructor.vmap(f)))
  }

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
