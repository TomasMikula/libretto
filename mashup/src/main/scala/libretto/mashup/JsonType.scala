package libretto.mashup

import libretto.mashup.dsl._
import zio.json.ast.Json

/** Witnesses that values of type [[A]] are directly representable in JSON. */
sealed trait JsonType[A] {
  def readJson(json: Json): Either[String, Value[A]]
}

object JsonType {
  case object JsonTypeText extends JsonType[Text] {
    override def readJson(json: Json): Either[String, Value[Text]] =
      json match {
        case Json.Str(s) => Right(Value.text(s))
        case _           => Left(s"Expected string, but got '${json.toString()}`")
      }
  }

  case object JsonTypeFloat64 extends JsonType[Float64] {
    override def readJson(json: Json): Either[String, Value[Float64]] =
      json match {
        case Json.Num(value) =>
          val d = value.doubleValue()
          val value1 = java.math.BigDecimal.valueOf(d)
          (value1 compareTo value) match {
            case 0 => Right(Value.float64(d))
            case _ => Left(s"The JSON number $value cannot be represented as Float64 without loss of precision (got ${java.lang.Double.toString(d)}).")
          }
        case _ =>
          Left(s"Expected Float64, but got '${json.toString()}'")
      }
  }

  case object JsonTypeEmptyRecord extends JsonType[Record] {
    override def readJson(json: Json): Either[String, Value[Record]] =
      json match {
        case Json.Obj(_) => Right(Value.emptyRecord)
        case _           => Left(s"Expected object, but got '${json.toString()}'")
      }
  }

  case class JsonTypeRecord[A, Name <: String, T](
    init: JsonType[A],
    name: Name,
    typ: JsonType[T],
  ) extends JsonType[A ## (Name of T)] {
    override def readJson(json: Json): Either[String, Value[A ## of[Name, T]]] =
      ???
  }

  given jsonTypeText: JsonType[Text] =
    JsonTypeText

  given jsonTypeFloat64: JsonType[Float64] =
    JsonTypeFloat64

  given jsonTypeEmptyRecord: JsonType[Record] =
    JsonTypeEmptyRecord

  given jsonTypeRecord[A, Name <: String, T](using
    A: JsonType[A],
    N: ConstValue[Name],
    T: JsonType[T],
  ): JsonType[A ## (Name of T)] =
    JsonTypeRecord(A, N.value, T)
}
