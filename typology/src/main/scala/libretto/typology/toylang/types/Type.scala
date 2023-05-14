package libretto.typology.toylang.types

import libretto.typology.kinds._

object Type {
  def unit: Type   = TypeExpr.unit
  def int: Type    = TypeExpr.int
  def string: Type = TypeExpr.string

  def pair(a: Type, b: Type): Type =
    TypeExpr(generic.TypeExpr.pair(a, b))

  def sum(a: Type, b: Type): Type =
    TypeExpr(generic.TypeExpr.sum(a, b))

  def fix(f: TypeFun[●, ●]): Type =
    TypeFun.toExpr(TypeFun.fix(f))

  def recCall(a: Type, b: Type): Type =
    TypeExpr(generic.TypeExpr.recCall(a, b))

  def abstractType(label: AbstractTypeLabel): Type =
    TypeExpr(generic.TypeExpr.abstractType(label))

  def typeMismatch(a: Type, b: Type): Type =
    TypeExpr(generic.TypeExpr.typeMismatch(a, b))
}
