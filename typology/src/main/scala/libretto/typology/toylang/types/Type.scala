package libretto.typology.toylang.types

import libretto.lambda.Tupled.*
import libretto.typology.kinds._

type Type[V] = TypeExpr[TypeConstructor[V, _, _], ○, ●]

object Type {
  def unit[V]: Type[V]   = TypeExpr.Primitive(TypeConstructor.UnitType())
  def int[V]: Type[V]    = TypeExpr.Primitive(TypeConstructor.IntType())
  def string[V]: Type[V] = TypeExpr.Primitive(TypeConstructor.StringType())

  def pair[V]: TypeExpr[TypeConstructor[V, _, _], ● × ●, ●] =
    TypeExpr.Primitive(TypeConstructor.Pair())

  def pair[V](a: Type[V], b: Type[V]): Type[V] =
    TypeExpr.App(
      TypeConstructor.Pair(),
      PartialArgs.introBoth(
        PartialArgs(a),
        PartialArgs(b),
      ),
    )

  def sum[V]: TypeExpr[TypeConstructor[V, _, _], ● × ●, ●] =
    TypeExpr.Primitive(TypeConstructor.Sum())

  def sum[V](a: Type[V], b: Type[V]): Type[V] =
    TypeExpr.App(
      TypeConstructor.Sum(),
      PartialArgs.introBoth(
        PartialArgs(a),
        PartialArgs(b),
      ),
    )

  def fix[V](f: TypeFun[TypeConstructor[V, _, _], ●, ●]): Type[V] =
    TypeExpr.Primitive(TypeConstructor.Fix(f.pre, f.expr))

  def recCall[V](a: Type[V], b: Type[V]): Type[V] =
    TypeExpr.App(
      TypeConstructor.RecCall(),
      PartialArgs.introBoth(
        PartialArgs(a),
        PartialArgs(b),
      ),
    )

  def abstractType[V](label: V): Type[V] =
    TypeExpr.Primitive(TypeConstructor.AbstractType(label))

  def typeMismatch[V](a: Type[V], b: Type[V]): Type[V] =
    TypeExpr.Primitive(TypeConstructor.TypeMismatch(a, b))

  def forbiddenSelfReference[V](v: V): Type[V] =
    TypeExpr.Primitive(TypeConstructor.ForbiddenSelfRef(v))

  object Pair {
    def unapply[V](t: Type[V]): Option[(Type[V], Type[V])] =
      t match {
        case TypeExpr.App(TypeConstructor.Pair(), args) =>
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
        case TypeExpr.App(TypeConstructor.Sum(), args) =>
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
        case TypeExpr.App(TypeConstructor.RecCall(), args) =>
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
        case TypeExpr.Primitive(TypeConstructor.AbstractType(v)) => Some(v)
        case _ => None
      }
  }

  type Fun[V, K, L] = TypeFun[TypeConstructor[V, _, _], K, L]

  object Fun {
    import TypeFun.{fromExpr, toExpr}

    def unit[V]: Type.Fun[V, ○, ●] =
      fromExpr(Type.unit)

    def int[V]: Type.Fun[V, ○, ●] =
      fromExpr(Type.int)

    def string[V]: Type.Fun[V, ○, ●] =
      fromExpr(Type.string)

    def pair[V]: Type.Fun[V, ● × ●, ●] =
      fromExpr(Type.pair)

    def pair[V](a: Type.Fun[V, ○, ●], b: Type.Fun[V, ○, ●]): Type.Fun[V, ○, ●] =
      fromExpr(Type.pair(toExpr(a), toExpr(b)))

    def pair1[V](a: Type[V]): Type.Fun[V, ●, ●] =
      fromExpr(
        TypeExpr.App(
          TypeConstructor.Pair(),
          PartialArgs.introFst(PartialArgs(a)),
        )
      )

    def pair1[V](a: Type.Fun[V, ○, ●]): Type.Fun[V, ●, ●] =
      pair1(toExpr(a))

    def pair2[V](b: Type[V]): Type.Fun[V, ●, ●] =
      fromExpr(
        TypeExpr.App(
          TypeConstructor.Pair(),
          PartialArgs.introSnd(PartialArgs(b)),
        )
      )

    def pair2[V](b: Type.Fun[V, ○, ●]): Type.Fun[V, ●, ●] =
      pair2(toExpr(b))

    def sum[V]: Type.Fun[V, ● × ●, ●] =
      fromExpr(TypeExpr.Primitive(TypeConstructor.Sum()))

    def sum[V](a: Type.Fun[V, ○, ●], b: Type.Fun[V, ○, ●]): Type.Fun[V, ○, ●] =
      fromExpr(Type.sum(toExpr(a), toExpr(b)))

    def sum1[V](a: Type[V]): Type.Fun[V, ●, ●] =
      fromExpr(
        TypeExpr.App(
          TypeConstructor.Sum(),
          PartialArgs.introFst(PartialArgs(a)),
        )
      )

    def sum1[V](a: Type.Fun[V, ○, ●]): Type.Fun[V, ●, ●] =
      sum1(toExpr(a))

    def sum2[V](b: Type[V]): Type.Fun[V, ●, ●] =
      fromExpr(
        TypeExpr.App(
          TypeConstructor.Sum(),
          PartialArgs.introSnd(PartialArgs(b)),
        )
      )

    def fix[V](f: Type.Fun[V, ●, ●]): Type.Fun[V, ○, ●] =
      fromExpr(Type.fix(f))

    def pfix[V](f: Type.Fun[V, ● × ●, ●]): Type.Fun[V, ●, ●] =
      fromExpr(TypeExpr.Primitive(TypeConstructor.PFix(f.pre, f.expr)))

    def abstractType[V](name: V): Type.Fun[V, ○, ●] =
      fromExpr(TypeExpr.Primitive(TypeConstructor.AbstractType(name)))
  }
}
