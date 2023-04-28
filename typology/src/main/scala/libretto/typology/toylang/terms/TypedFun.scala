package libretto.typology.toylang.terms

import libretto.typology.toylang.types.Type

final case class TypedFun[A, B](
  ta: Type,
  f: FunT[TypedFun, A, B],
  tb: Type,
)
