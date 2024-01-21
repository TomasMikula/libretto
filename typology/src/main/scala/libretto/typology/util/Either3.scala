package libretto.typology.util

enum Either3[+A, +B, +C] {
  case Left(value: A)
  case Middle(value: B)
  case Right(value: C)
}
