package libretto.mashup

import libretto.mashup.dsl._
import zio.Chunk
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

  case class JsonTypeObject[A](typ: ObjectType[A]) extends JsonType[A] {
    override def readJson(json: Json): Either[String, Value[A]] =
      json match {
        case Json.Obj(fields) => typ.readJson(fields)
        case _                => Left(s"Expected object, but got '${json.toString()}'")
      }
  }

  sealed trait ObjectType[A] {
    def readJson(fields: Chunk[(String, Json)]): Either[String, Value[A]]
  }

  object ObjectType {

    case object EmptyRecord extends ObjectType[Record] {
      override def readJson(fields: Chunk[(String, Json)]): Either[String, Value[Record]] =
        Right(Value.emptyRecord)
    }

    case class NonEmptyRecord[A, Name <: String, T](
      init: ObjectType[A],
      name: Name,
      typ: JsonType[T],
    ) extends ObjectType[A ## (Name of T)] {
      override def readJson(fields: Chunk[(String, Json)]): Either[String, Value[A ## of[Name, T]]] =
        for {
          initValue <- init.readJson(fields)
          lastValue <- readField(fields)
        } yield Value.extendRecord(initValue, name, lastValue)

      private def readField(fields: Chunk[(String, Json)]): Either[String, Value[T]] =
        fields.collectFirst { case (k, v) if k == name => v } match {
          case None       => Left(s"Missing field \"${name}\" in ${Json.Obj(fields).toString()}")
          case Some(json) => typ.readJson(json)
        }
    }

    given objectTypeEmptyRecord: ObjectType[Record] =
      EmptyRecord

    given objectTypeNonEmptyRecord[A, Name <: String, T](using
      A: ObjectType[A],
      N: ConstValue[Name],
      T: JsonType[T],
    ): ObjectType[A ## (Name of T)] =
      NonEmptyRecord(A, N.value, T)
  }

  given jsonTypeText: JsonType[Text] =
    JsonTypeText

  given jsonTypeFloat64: JsonType[Float64] =
    JsonTypeFloat64

  given jsonTypeObject[A](using typ: ObjectType[A]): JsonType[A] =
    JsonTypeObject(typ)
}
