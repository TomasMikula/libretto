package libretto.lambda.util

/** Evidence that `T` is a singleton type, together with the single value of type `T`. */
abstract case class SingletonType[T](value: T) {
  def witness: T =:= value.type

  def as[U](using ev: T =:= U): SingletonType[U] =
    ev.substituteCo(this)
}

object SingletonType {
  def apply(x: Any): SingletonType[x.type] =
    new SingletonType[x.type](x) {
      override def witness: x.type =:= value.type = summon
    }

  inline given compiletimeConstant[T]: SingletonType[T] = {
    val t = scala.compiletime.constValue[T]
    scala.compiletime.summonInline[t.type =:= T]
      .substituteCo(
        SingletonType(t)
      )
  }

  def testEqual[A <: String, B <: String](
    a: SingletonType[A],
    b: SingletonType[B],
  ): Option[A =:= B] =
    Option.when(a.value == b.value) {
      summon[A =:= A].asInstanceOf[A =:= B]
    }
}
