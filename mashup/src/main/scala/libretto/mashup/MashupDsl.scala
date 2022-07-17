package libretto.mashup

import libretto.StarterKit.{dsl => StarterDsl}
import libretto.StarterKit.dsl.{-⚬, =⚬, |*|, |+|, One, Val}
import libretto.scalasource

trait MashupDsl {
  type Fun[A, B]

  type EmptyResource

  type or[A, B]

  /** Higher-order function, i.e. one that occurs on input or output of [[Fun]]s. */
  type -->[A, B]

  type Text

  type Float64

  type Expr[A]

  type of[Name <: String, T]

  type Record[Fields]

  type ##[A, B]

  type |&|[A, B]

  type Unlimited[A]


  def fun[A, B](f: Expr[A] => Expr[B]): Fun[A, B]

  def closure[A, B](f: Expr[A] => Expr[B]): Expr[A --> B]

  def id[A]: Fun[A, A]

  def left[A, B]: Fun[A, A or B]

  def right[A, B]: Fun[B, A or B]

  import StarterDsl.$._

  val Record: Records

  trait Records {
    def empty(using pos: scalasource.Position): Expr[Record[EmptyResource]]

    def field[N <: String & Singleton, T](field: (N, Expr[T])): Expr[Record[N of T]]
  }

  val Float64: Float64s

  trait Float64s {
    def apply(value: Double)(using pos: scalasource.Position): Expr[Float64]

    def add(a: Expr[Float64], b: Expr[Float64])(using pos: scalasource.Position): Expr[Float64]

    def subtract(a: Expr[Float64], b: Expr[Float64])(using pos: scalasource.Position): Expr[Float64]

    def negate(a: Expr[Float64])(using pos: scalasource.Position): Expr[Float64]

    def multiply(a: Expr[Float64], b: Expr[Float64])(using pos: scalasource.Position): Expr[Float64]

    def divide(a: Expr[Float64], b: Expr[Float64])(using pos: scalasource.Position): Expr[Float64]
  }

  val Expr: Exprs

  trait Exprs {
    def eliminateSecond[A](a: Expr[A], empty: Expr[EmptyResource])(pos: scalasource.Position): Expr[A]

    def extendRecord[A, N <: String, T](
      init: Expr[Record[A]],
      last: (N, Expr[T]),
    )(
      pos: scalasource.Position,
    ): Expr[Record[A ## (N of T)]]
  }

  val Unlimited: Unlimiteds

  trait Unlimiteds {
    def map[A, B](f: Fun[A, B]): Fun[Unlimited[A], Unlimited[B]]
  }

  val as: SingleFieldExtractor

  trait SingleFieldExtractor {
    def unapply[N <: String & Singleton, T](
      field: Expr[Record[N of T]],
    )(using
      N: ConstValue[N],
    ): (N, Expr[T])
  }

  extension [A](a: Expr[A]) {
    def alsoElim(empty: Expr[EmptyResource])(using
      pos: scalasource.Position,
    ): Expr[A] =
      Expr.eliminateSecond(a, empty)(pos)
  }

  extension [A](a: Expr[Record[A]]) {
    def field[N <: String & Singleton, T](field: (N, Expr[T]))(using
      pos: scalasource.Position,
    ): Expr[Record[A ## (N of T)]] =
      Expr.extendRecord(a, field)(pos)
  }

  extension (self: Expr[Float64]) {
    def +(that: Expr[Float64])(using pos: scalasource.Position): Expr[Float64] =
      Float64.add(self, that)

    def +(that: Double)(using pos: scalasource.Position): Expr[Float64] =
      self + Float64(that)

    def -(that: Expr[Float64])(using pos: scalasource.Position): Expr[Float64] =
      Float64.subtract(self, that)

    def -(that: Double)(using pos: scalasource.Position): Expr[Float64] =
      self - Float64(that)

    def unary_-(using pos: scalasource.Position): Expr[Float64] =
      Float64.negate(self)

    def *(that: Expr[Float64])(using pos: scalasource.Position): Expr[Float64] =
      Float64.multiply(self, that)

    def *(that: Double)(using pos: scalasource.Position): Expr[Float64] =
      self * Float64(that)

    def /(that: Expr[Float64])(using pos: scalasource.Position): Expr[Float64] =
      Float64.divide(self, that)

    def /(that: Double)(using pos: scalasource.Position): Expr[Float64] =
      self / Float64(that)
  }
}
