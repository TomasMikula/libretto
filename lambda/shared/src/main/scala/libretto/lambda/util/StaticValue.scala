package libretto.lambda.util

class StaticValue[T] private(val value: T)

object StaticValue {
  private def make[T](t: T): StaticValue[T] =
    StaticValue(t)

  inline given get[T]: StaticValue[T] =
    make(scala.compiletime.constValue[T])
}
