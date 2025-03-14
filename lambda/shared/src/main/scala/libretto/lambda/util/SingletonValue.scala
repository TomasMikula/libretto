package libretto.lambda.util

/** Value of type `T` together with evidence that `T` is a singleton type. */
abstract case class SingletonValue[T](value: T) {
  def witness: T =:= value.type

  def as[U](using ev: T =:= U): SingletonValue[U] =
    ev.substituteCo(this)
}

object SingletonValue {
  def apply(x: Any): SingletonValue[x.type] =
    new SingletonValue[x.type](x) {
      override def witness: x.type =:= value.type = summon
    }

  inline given get[T]: SingletonValue[T] = {
    val t = scala.compiletime.constValue[T]
    scala.compiletime.summonInline[t.type =:= T]
      .substituteCo(
        SingletonValue(t)
      )
  }
}
