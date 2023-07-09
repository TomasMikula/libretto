package libretto.typology.toylang.types

import libretto.typology.kinds._

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
}
