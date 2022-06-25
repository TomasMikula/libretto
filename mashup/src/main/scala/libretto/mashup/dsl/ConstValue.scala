package libretto.mashup.dsl

final case class ConstValue[T](value: T)

object ConstValue {
  inline implicit def constValue[T]: ConstValue[T] =
    ConstValue(scala.compiletime.constValue[T])
}
