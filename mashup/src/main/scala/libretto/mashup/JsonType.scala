package libretto.mashup

import libretto.mashup.dsl._
import zio.Chunk
import zio.json.ast.Json

/** Witnesses that values of type [[A]] are directly representable in JSON. */
sealed trait JsonType[A] {
  def readJson(json: Json)(using rt: Runtime): Either[String, rt.Value[A]]
}

object JsonType {
  case object JsonTypeText extends JsonType[Text] {
    override def readJson(json: Json)(using rt: Runtime): Either[String, rt.Value[Text]] =
      json match {
        case Json.Str(s) => Right(rt.Value.text(s))
        case _           => Left(s"Expected string, but got '${json.toString()}`")
      }
  }

  case object JsonTypeFloat64 extends JsonType[Float64] {
    override def readJson(json: Json)(using rt: Runtime): Either[String, rt.Value[Float64]] =
      json match {
        case Json.Num(value) =>
          val d = value.doubleValue()
          val value1 = java.math.BigDecimal.valueOf(d)
          (value1 compareTo value) match {
            case 0 => Right(rt.Value.float64(d))
            case _ => Left(s"The JSON number $value cannot be represented as Float64 without loss of precision (got ${java.lang.Double.toString(d)}).")
          }
        case _ =>
          Left(s"Expected Float64, but got '${json.toString()}'")
      }
  }

  case class JsonTypeObject[A](typ: ObjectType[A]) extends JsonType[A] {
    override def readJson(json: Json)(using rt: Runtime): Either[String, rt.Value[A]] =
      json match {
        case Json.Obj(fields) => typ.readJson(fields)
        case _                => Left(s"Expected object, but got '${json.toString()}'")
      }
  }

  sealed trait ObjectType[A] {
    def readJson(fields: Chunk[(String, Json)])(using rt: Runtime): Either[String, rt.Value[A]]
  }

  object ObjectType {

    case object EmptyRecord extends ObjectType[Record[EmptyResource]] {
      override def readJson(fields: Chunk[(String, Json)])(using
        rt: Runtime,
      ): Either[String, rt.Value[Record[EmptyResource]]] =
        Right(rt.Value.emptyRecord)
    }

    case class SingleFieldRecord[Name <: String & Singleton, T](
      name: Name,
      typ: JsonType[T],
    ) extends ObjectType[Record[Name of T]] {
      override def readJson(fields: Chunk[(String, Json)])(using rt: Runtime): Either[String, rt.Value[Record[Name of T]]] =
        readField(fields, name, typ)
          .map(rt.Value.record(name, _))
    }

    case class NonEmptyRecord[A, Name <: String, T](
      init: ObjectType[Record[A]],
      name: Name,
      typ: JsonType[T],
    ) extends ObjectType[Record[A ### (Name of T)]] {
      override def readJson(fields: Chunk[(String, Json)])(using rt: Runtime): Either[String, rt.Value[Record[A ### (Name of T)]]] =
        for {
          initValue <- init.readJson(fields)
          lastValue <- readField(fields, name, typ)
        } yield rt.Value.extendRecord(initValue, name, lastValue)
    }

    private def readField[T](fields: Chunk[(String, Json)], key: String, typ: JsonType[T])(using rt: Runtime): Either[String, rt.Value[T]] =
      fields.collectFirst { case (k, v) if k == key => v } match {
        case None       => Left(s"Missing field \"${key}\" in ${Json.Obj(fields).toString()}")
        case Some(json) => typ.readJson(json)
      }

    given objectTypeEmptyRecord: ObjectType[Record[EmptyResource]] =
      EmptyRecord

    given objectTypeSingleFieldRecord[Name <: String & Singleton, T](using
      N: ConstValue[Name],
      T: JsonType[T],
    ): ObjectType[Record[Name of T]] =
      SingleFieldRecord(N.value, T)

    given objectTypeNonEmptyRecord[A, Name <: String, T](using
      A: ObjectType[Record[A]],
      N: ConstValue[Name],
      T: JsonType[T],
    ): ObjectType[Record[A ### (Name of T)]] =
      NonEmptyRecord(A, N.value, T)
  }

  given jsonTypeText: JsonType[Text] =
    JsonTypeText

  given jsonTypeFloat64: JsonType[Float64] =
    JsonTypeFloat64

  given jsonTypeObject[A](using typ: ObjectType[A]): JsonType[A] =
    JsonTypeObject(typ)
}
