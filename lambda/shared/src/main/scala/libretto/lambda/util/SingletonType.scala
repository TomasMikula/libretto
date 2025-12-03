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

  def testEqualByte[A <: Byte, B <: Byte](
    a: SingletonType[A],
    b: SingletonType[B],
  ): Option[A =:= B] =
    Option.when(a.value == b.value) {
      summon[A =:= A].asInstanceOf[A =:= B]
    }

  def testEqualShort[A <: Short, B <: Short](
    a: SingletonType[A],
    b: SingletonType[B],
  ): Option[A =:= B] =
    Option.when(a.value == b.value) {
      summon[A =:= A].asInstanceOf[A =:= B]
    }

  def testEqualInt[A <: Int, B <: Int](
    a: SingletonType[A],
    b: SingletonType[B],
  ): Option[A =:= B] =
    Option.when(a.value == b.value) {
      summon[A =:= A].asInstanceOf[A =:= B]
    }

  def testEqualLong[A <: Long, B <: Long](
    a: SingletonType[A],
    b: SingletonType[B],
  ): Option[A =:= B] =
    Option.when(a.value == b.value) {
      summon[A =:= A].asInstanceOf[A =:= B]
    }

  def testEqualFloat[A <: Float, B <: Float](
    a: SingletonType[A],
    b: SingletonType[B],
  ): Option[A =:= B] =
    Option.when(a.value == b.value) {
      summon[A =:= A].asInstanceOf[A =:= B]
    }

  def testEqualDouble[A <: Double, B <: Double](
    a: SingletonType[A],
    b: SingletonType[B],
  ): Option[A =:= B] =
    Option.when(a.value == b.value) {
      summon[A =:= A].asInstanceOf[A =:= B]
    }

  def testEqualBoolean[A <: Boolean, B <: Boolean](
    a: SingletonType[A],
    b: SingletonType[B],
  ): Option[A =:= B] =
    Option.when(a.value == b.value) {
      summon[A =:= A].asInstanceOf[A =:= B]
    }

  def testEqualChar[A <: Char, B <: Char](
    a: SingletonType[A],
    b: SingletonType[B],
  ): Option[A =:= B] =
    Option.when(a.value == b.value) {
      summon[A =:= A].asInstanceOf[A =:= B]
    }

  def testEqualString[A <: String, B <: String](
    a: SingletonType[A],
    b: SingletonType[B],
  ): Option[A =:= B] =
    Option.when(a.value == b.value) {
      summon[A =:= A].asInstanceOf[A =:= B]
    }
}
