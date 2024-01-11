package libretto.typology.toylang.types

import libretto.lambda.Tupled.*
import libretto.typology.kinds._

type Type[V] = TypeExpr[V, ○, ●]

object Type {
  def unit[V]: Type[V]   = TypeExpr.unit
  def int[V]: Type[V]    = TypeExpr.int
  def string[V]: Type[V] = TypeExpr.string

  def pair[V](a: Type[V], b: Type[V]): Type[V] =
    TypeExpr.pair(a, b)

  def sum[V](a: Type[V], b: Type[V]): Type[V] =
    TypeExpr.sum(a, b)

  def fix[V](f: TypeFun[V, ●, ●]): Type[V] =
    TypeFun.toExpr(TypeFun.fix(f))

  def recCall[V](a: Type[V], b: Type[V]): Type[V] =
    TypeExpr.recCall(a, b)

  def abstractType[V](label: V): Type[V] =
    TypeExpr.abstractType(label)

  def typeMismatch[V](a: Type[V], b: Type[V]): Type[V] =
    TypeExpr.typeMismatch(a, b)

  def forbiddenSelfReference[V](v: V): Type[V] =
    TypeExpr.forbiddenSelfReference(v)

  object Pair {
    def unapply[V](t: Type[V]): Option[(Type[V], Type[V])] =
      t match {
        case TypeExpr.App(TypeExpr.Primitive.Pair(), args) =>
          PartialArgs.extract(args) match
            case Atom(a) <*> Atom(b) =>
              Some((a, b))
        case _ =>
          None
      }
  }

  object Sum {
    def unapply[V](t: Type[V]): Option[(Type[V], Type[V])] =
      t match {
        case TypeExpr.App(TypeExpr.Primitive.Sum(), args) =>
          PartialArgs.extract(args) match
            case Atom(a) <*> Atom(b) =>
              Some((a, b))
        case _ =>
          None
      }
  }

  object RecCall {
    def unapply[V](t: Type[V]): Option[(Type[V], Type[V])] =
      t match {
        case TypeExpr.App(TypeExpr.Primitive.RecCall(), args) =>
          PartialArgs.extract(args) match
            case Atom(a) <*> Atom(b) =>
              Some((a, b))
        case _ =>
          None
      }
  }

  object AbstractType {
    def unapply[V](t: Type[V]): Option[V] =
      t match {
        case TypeExpr.Wrap(TypeExpr.Primitive.AbstractType(v)) => Some(v)
        case _ => None
      }
  }
}
