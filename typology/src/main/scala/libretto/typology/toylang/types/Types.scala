package libretto.typology.toylang.types

enum Types[V]:
  case SingleType(value: Type[V])
  case Product(l: Types[V], r: Types[V])
  case KindMismatch(l: Types[V], r: Types[V])
