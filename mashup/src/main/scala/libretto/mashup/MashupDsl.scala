package libretto.mashup

import libretto.StarterKit.{dsl => StarterDsl}
import libretto.StarterKit.dsl.{-⚬, =⚬, |*|, |+|, One, Val}
import libretto.scalasource
import scala.annotation.targetName

trait MashupDsl {
  type Fun[A, B]

  type **[A, B]

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

  /** Evidence that `A` is a _value type_. */
  type ValueType[A]

  /** Evidence that the type `A` has an option named `K` of type `T`. */
  trait AbstractPick[A, K <: String & Singleton] {
    type T

    def asFun: Fun[A, T]
  }

  type Pick[A, K <: String & Singleton] <: AbstractPick[A, K]

  type Picked[A, K <: String & Singleton, V] = Pick[A, K] { type T = V }


  def fun[A, B](f: Expr[A] => Expr[B])(using pos: scalasource.Position): Fun[A, B]

  def closure[A, B](f: Expr[A] => Expr[B])(using pos: scalasource.Position): Expr[A --> B]

  def id[A]: Fun[A, A]

  def left[A, B]: Fun[A, A or B]

  def right[A, B]: Fun[B, A or B]

  def eval[A, B]: Fun[(A --> B) ** A, B]

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

  val Text: Texts

  trait Texts {
    def apply(value: String)(using pos: scalasource.Position): Expr[Text]
  }

  val Expr: Exprs

  trait Exprs {
    def pair[A, B](a: Expr[A], b: Expr[B])(pos: scalasource.Position): Expr[A ** B]

    def unit(using pos: scalasource.Position): Expr[EmptyResource]

    def eliminateSecond[A](a: Expr[A], empty: Expr[EmptyResource])(pos: scalasource.Position): Expr[A]

    def awaitSecond[A, B](a: Expr[A], b: Expr[B])(pos: scalasource.Position)(using
      ValueType[A],
      ValueType[B],
    ): Expr[A]

    def extendRecord[A, N <: String, T](
      init: Expr[Record[A]],
      last: (N, Expr[T]),
    )(
      pos: scalasource.Position,
    ): Expr[Record[A ## (N of T)]]

    def map[A, B](a: Expr[A], f: Fun[A, B])(pos: scalasource.Position): Expr[B]

    def debugPrint[A](s: String, expr: Expr[A])(using ValueType[A]): Expr[A]
  }

  val Unlimited: Unlimiteds

  trait Unlimiteds {
    def discard[A]: Fun[Unlimited[A], EmptyResource]
    def getSingle[A]: Fun[Unlimited[A], A]
    def split[A]: Fun[Unlimited[A], Unlimited[A] ** Unlimited[A]]
    def duplicate[A]: Fun[Unlimited[A], Unlimited[Unlimited[A]]]
    def map[A, B](f: Fun[A, B]): Fun[Unlimited[A], Unlimited[B]]
  }

  val ** : PairExtractor

  trait PairExtractor {
    def unapply[A, B](ab: Expr[A ** B])(using pos: scalasource.Position): (Expr[A], Expr[B])
  }

  val as  : SingleFieldExtractor
  val ### : RecordExtractor

  trait SingleFieldExtractor {
    def unapply[N <: String & Singleton, T](
      field: Expr[Record[N of T]],
    )(using
      N: ConstValue[N],
    ): (N, Expr[T])
  }

  trait RecordExtractor {
    def unapply[A, B](rec: Expr[Record[A ## B]])(using pos: scalasource.Position): (Expr[Record[A]], Expr[Record[B]])
  }

  extension [A](a: Expr[A]) {
    def **[B](b: Expr[B])(using pos: scalasource.Position): Expr[A ** B] =
      Expr.pair(a, b)(pos)

    def pick[K <: String & Singleton](using pick: Pick[A, K])(using
      pos: scalasource.Position,
    ): Expr[pick.T] =
      Expr.map(a, pick.asFun)(pos)

    def alsoElim(empty: Expr[EmptyResource])(using
      pos: scalasource.Position,
    ): Expr[A] =
      Expr.eliminateSecond(a, empty)(pos)

    def debugPrint(msg: String)(using ValueType[A]): Expr[A] =
      Expr.debugPrint(msg, a)
  }

  extension [A: ValueType](a: Expr[A]) {
    def alsoAwait[B: ValueType](b: Expr[B])(using pos: scalasource.Position): Expr[A] =
      Expr.awaitSecond(a, b)(pos)
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

  extension [A, B](f: Fun[A, B]) {
    @targetName("applyFun")
    def apply(a: Expr[A])(using pos: scalasource.Position): Expr[B] =
      Expr.map(a, f)(pos)
  }

  extension [A, B](f: Expr[A --> B]) {
    @targetName("evalFunExpr")
    def apply(a: Expr[A])(using pos: scalasource.Position): Expr[B] =
      Expr.map((f ** a)(using pos), eval)(pos)
  }

  extension [A](self: Expr[Unlimited[A]]) {
    def split(using pos: scalasource.Position): (Expr[Unlimited[A]], Expr[Unlimited[A]]) =
      **.unapply(Unlimited.split[A](self)(using pos))(using pos)

    def get(using pos: scalasource.Position): Expr[A] =
      Expr.map(self, Unlimited.getSingle)(pos)
  }

  given singleOptionPick[K <: String & Singleton, V]: Picked[K of V, K, V]
  given choicePickLeft[A, K <: String & Singleton, V, B](using ev: Picked[A, K, V]): Picked[A |&| B, K, V]
  given choicePickRight[A, B, K <: String & Singleton, V](using ev: Picked[B, K, V]): Picked[A |&| B, K, V]

  given valueTypeText: ValueType[Text]
  given valueTypeFloat64: ValueType[Float64]
  given valueTypeSingleFieldRecord[N <: String & Singleton, T](using ConstValue[N], ValueType[T]): ValueType[Record[N of T]]
  given valueTypeRecord[A, N <: String & Singleton, T](using ValueType[A], ConstValue[N], ValueType[T]): ValueType[Record[A ## (N of T)]]
}
