package libretto.typology.toylang.terms

import libretto.typology.toylang.types.Type

sealed trait TypedFun[A, B]

object TypedFun {
  case class Id[A](typ: Type) extends TypedFun[A, A]
  case class AndThen[A, X, B](f: TypedFun[A, X], tx: Type, g: TypedFun[X, B]) extends TypedFun[A, B]

  def id[A](typ: Type): TypedFun[A, A] = Id(typ)
  def andThen[A, X, B](f: TypedFun[A, X], tx: Type, g: TypedFun[X, B]): TypedFun[A, B] = AndThen(f, tx, g)
}
