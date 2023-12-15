package libretto.typology.toylang.types

import libretto.lambda.SymmetricMonoidalCategory
import libretto.typology.kinds._

trait TypeAlgebra[V, ==>[_, _]] {
  type Type
  type <*>[_, _]
  type None

  given category: SymmetricMonoidalCategory[==>, <*>, None]

  def unit   : None ==> Type
  def int    : None ==> Type
  def string : None ==> Type

  def pair    : (Type <*> Type) ==> Type
  def sum     : (Type <*> Type) ==> Type
  def recCall : (Type <*> Type) ==> Type

  // XXX: crutches
  def fix(f: TypeFun[V, ●, ●]): None ==> Type
  def pfix(f: TypeFun[V, ● × ●, ●]): Type ==> Type

  def abstractTypeName(name: V): None ==> Type
}

object TypeAlgebra {
  type Of[V, ==>[_, _], T, P[_, _], U] =
    TypeAlgebra[V, ==>] {
      type Type      = T
      type <*>[a, b] = P[a, b]
      type None      = U
    }
}
