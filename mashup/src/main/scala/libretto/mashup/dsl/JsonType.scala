package libretto.mashup.dsl

/** Witnesses that values of type [[A]] are directly representable in JSON. */
sealed trait JsonType[A]

object JsonType {
  case object JsonTypeString extends JsonType[String]

  case object JsonTypeFloat64 extends JsonType[Float64]

  case object JsonTypeEmptyRecord extends JsonType[Record]

  case class JsonTypeRecord[A <: AbstractRecord, Name <: String, T](
    init: JsonType[A],
    name: Name,
    typ: JsonType[T],
  ) extends JsonType[A ## (Name of T)]

  given jsonTypeString: JsonType[String] =
    JsonTypeString

  given jsonTypeFloat64: JsonType[Float64] =
    JsonTypeFloat64

  given jsonTypeEmptyRecord: JsonType[Record] =
    JsonTypeEmptyRecord

  given jsonTypeRecord[A <: AbstractRecord, Name <: String, T](using
    A: JsonType[A],
    N: ConstValue[Name],
    T: JsonType[T],
  ): JsonType[A ## (Name of T)] =
    JsonTypeRecord(A, N.value, T)
}
