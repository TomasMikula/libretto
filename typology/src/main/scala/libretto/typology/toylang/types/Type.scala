package libretto.typology.toylang.types

import libretto.typology.kinds._
import libretto.typology.toylang.types.generic.{TypeExpr => gte}

type Type[V] = TypeExpr[V, ○, ●]

object Type {
  def unit[V]: Type[V]   = TypeExpr.unit
  def int[V]: Type[V]    = TypeExpr.int
  def string[V]: Type[V] = TypeExpr.string

  def pair[V](a: Type[V], b: Type[V]): Type[V] =
    TypeExpr(generic.TypeExpr.pair(a, b))

  def sum[V](a: Type[V], b: Type[V]): Type[V] =
    TypeExpr(generic.TypeExpr.sum(a, b))

  def fix[V](f: TypeFun[V, ●, ●]): Type[V] =
    TypeFun.toExpr(TypeFun.fix(f))

  def recCall[V](a: Type[V], b: Type[V]): Type[V] =
    TypeExpr(generic.TypeExpr.recCall(a, b))

  def abstractType[V](label: V): Type[V] =
    TypeExpr(generic.TypeExpr.abstractType(label))

  def typeMismatch[V](a: Type[V], b: Type[V]): Type[V] =
    TypeExpr(generic.TypeExpr.typeMismatch(a, b))

  object Pair {
    def unapply[V](t: Type[V]): Option[(Type[V], Type[V])] =
      t.value match {
        case gte.BiApp(gte.Pair(), a, b) => Some(a, b)
        case _ => None
      }
  }

  object Sum {
    def unapply[V](t: Type[V]): Option[(Type[V], Type[V])] =
      t.value match {
        case gte.BiApp(gte.Sum(), a, b) => Some(a, b)
        case _ => None
      }
  }

  object RecCall {
    def unapply[V](t: Type[V]): Option[(Type[V], Type[V])] =
      t.value match {
        case gte.BiApp(gte.RecCall(), a, b) => Some(a, b)
        case _ => None
      }
  }

  object AbstractType {
    def unapply[V](t: Type[V]): Option[V] =
      t.value match {
        case gte.AbstractType(v) => Some(v)
        case _ => None
      }
  }
}
