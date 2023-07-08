package libretto.typology.toylang.types

import libretto.lambda.SymmetricMonoidalCategory
import libretto.typology.kinds._

trait TypeAlgebra[==>[_, _]] {
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

  // XXX: crutch
  def fix(f: TypeFun[●, ●]): None ==> Type
}

object TypeAlgebra {
  type With[==>[_, _], T, P[_, _], U] =
    TypeAlgebra[==>] {
      type Type      = T
      type <*>[a, b] = P[a, b]
      type None      = U
    }
}
