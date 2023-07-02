package libretto.mashup

import libretto.lambda.util.SourcePos
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

  type ###[A, B]

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

  type LambdaContext

  val fun: Funs

  trait Funs {
    def apply[A, B](using SourcePos)(f: LambdaContext ?=> Expr[A] => Expr[B]): Fun[A, B]
    def ?[A, B](using SourcePos)(f: LambdaContext ?=> Expr[A] => Expr[B])(using Affine[A]): Fun[A, B]
    def +[A, B](using SourcePos)(f: LambdaContext ?=> Expr[A] => Expr[B])(using Cosemigroup[A]): Fun[A, B]
    def *[A, B](using SourcePos)(f: LambdaContext ?=> Expr[A] => Expr[B])(using Comonoid[A]): Fun[A, B]
  }

  val closure: Closures

  trait Closures {
    def apply[A, B](using SourcePos, LambdaContext)(f: LambdaContext ?=> Expr[A] => Expr[B]): Expr[A --> B]
    def ?[A, B](using SourcePos, LambdaContext)(f: LambdaContext ?=> Expr[A] => Expr[B])(using Affine[A]): Expr[A --> B]
    def +[A, B](using SourcePos, LambdaContext)(f: LambdaContext ?=> Expr[A] => Expr[B])(using Cosemigroup[A]): Expr[A --> B]
    def *[A, B](using SourcePos, LambdaContext)(f: LambdaContext ?=> Expr[A] => Expr[B])(using Comonoid[A]): Expr[A --> B]
  }

  def id[A]: Fun[A, A]

  def left[A, B]: Fun[A, A or B]

  def right[A, B]: Fun[B, A or B]

  def eval[A, B]: Fun[(A --> B) ** A, B]

  val Record: Records

  trait Records {
    def empty(using SourcePos, LambdaContext): Expr[Record[EmptyResource]]

    def field[N <: String & Singleton, T](field: (N, Expr[T])): Expr[Record[N of T]]
  }

  val Float64: Float64s

  trait Float64s {
    def apply(value: Double)(using SourcePos, LambdaContext): Expr[Float64]

    def add(a: Expr[Float64], b: Expr[Float64])(using SourcePos, LambdaContext): Expr[Float64]

    def subtract(a: Expr[Float64], b: Expr[Float64])(using SourcePos, LambdaContext): Expr[Float64]

    def negate(a: Expr[Float64])(using SourcePos, LambdaContext): Expr[Float64]

    def multiply(a: Expr[Float64], b: Expr[Float64])(using SourcePos, LambdaContext): Expr[Float64]

    def divide(a: Expr[Float64], b: Expr[Float64])(using SourcePos, LambdaContext): Expr[Float64]
  }

  val Text: Texts

  trait Texts {
    def apply(value: String)(using SourcePos, LambdaContext): Expr[Text]
  }

  val Expr: Exprs

  trait Exprs {
    def pair[A, B](a: Expr[A], b: Expr[B])(pos: SourcePos)(using LambdaContext): Expr[A ** B]

    def unit(using SourcePos, LambdaContext): Expr[EmptyResource]

    def eliminateSecond[A](a: Expr[A], empty: Expr[EmptyResource])(pos: SourcePos)(using LambdaContext): Expr[A]

    def awaitSecond[A, B](a: Expr[A], b: Expr[B])(pos: SourcePos)(using
      ValueType[A],
      ValueType[B],
    )(using
      LambdaContext,
    ): Expr[A]

    def extendRecord[A, N <: String, T](
      init: Expr[Record[A]],
      last: (N, Expr[T]),
    )(
      pos: SourcePos,
    )(using
      LambdaContext,
    ): Expr[Record[A ### (N of T)]]

    def map[A, B](a: Expr[A], f: Fun[A, B])(pos: SourcePos)(using LambdaContext): Expr[B]

    def debugPrint[A](s: String, expr: Expr[A])(using ValueType[A])(using LambdaContext): Expr[A]
  }

  val Unlimited: Unlimiteds

  trait Unlimiteds {
    def discard[A]: Fun[Unlimited[A], EmptyResource]
    def getSingle[A]: Fun[Unlimited[A], A]
    def split[A]: Fun[Unlimited[A], Unlimited[A] ** Unlimited[A]]
    def duplicate[A]: Fun[Unlimited[A], Unlimited[Unlimited[A]]]
    def map[A, B](f: Fun[A, B]): Fun[Unlimited[A], Unlimited[B]]
  }

  given comonoidUnlimited[A]: Comonoid[Unlimited[A]]

  val ** : PairExtractor

  trait PairExtractor {
    def unapply[A, B](ab: Expr[A ** B])(using SourcePos, LambdaContext): (Expr[A], Expr[B])
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
    def unapply[A, B](rec: Expr[Record[A ### B]])(using SourcePos, LambdaContext): (Expr[Record[A]], Expr[Record[B]])
  }

  extension [A](a: Expr[A]) {
    def **[B](b: Expr[B])(using pos: SourcePos, ctx: LambdaContext): Expr[A ** B] =
      Expr.pair(a, b)(pos)

    def pick[K <: String & Singleton](using pick: Pick[A, K])(using
      pos: SourcePos,
      ctx: LambdaContext,
    ): Expr[pick.T] =
      Expr.map(a, pick.asFun)(pos)

    def alsoElim(empty: Expr[EmptyResource])(using
      pos: SourcePos,
      ctx: LambdaContext,
    ): Expr[A] =
      Expr.eliminateSecond(a, empty)(pos)

    def debugPrint(msg: String)(using ValueType[A])(using LambdaContext): Expr[A] =
      Expr.debugPrint(msg, a)
  }

  extension [A: ValueType](a: Expr[A]) {
    def alsoAwait[B: ValueType](b: Expr[B])(using pos: SourcePos, ctx: LambdaContext): Expr[A] =
      Expr.awaitSecond(a, b)(pos)
  }

  extension [A](a: Expr[Record[A]]) {
    def field[N <: String & Singleton, T](field: (N, Expr[T]))(using
      pos: SourcePos,
      ctx: LambdaContext,
    ): Expr[Record[A ### (N of T)]] =
      Expr.extendRecord(a, field)(pos)
  }

  extension (self: Expr[Float64]) {
    def +(that: Expr[Float64])(using pos: SourcePos, ctx: LambdaContext): Expr[Float64] =
      Float64.add(self, that)

    def +(that: Double)(using pos: SourcePos, ctx: LambdaContext): Expr[Float64] =
      self + Float64(that)

    def -(that: Expr[Float64])(using pos: SourcePos, ctx: LambdaContext): Expr[Float64] =
      Float64.subtract(self, that)

    def -(that: Double)(using pos: SourcePos, ctx: LambdaContext): Expr[Float64] =
      self - Float64(that)

    def unary_-(using pos: SourcePos, ctx: LambdaContext): Expr[Float64] =
      Float64.negate(self)

    def *(that: Expr[Float64])(using pos: SourcePos, ctx: LambdaContext): Expr[Float64] =
      Float64.multiply(self, that)

    def *(that: Double)(using pos: SourcePos, ctx: LambdaContext): Expr[Float64] =
      self * Float64(that)

    def /(that: Expr[Float64])(using pos: SourcePos, ctx: LambdaContext): Expr[Float64] =
      Float64.divide(self, that)

    def /(that: Double)(using pos: SourcePos, ctx: LambdaContext): Expr[Float64] =
      self / Float64(that)
  }

  extension [A, B](f: Fun[A, B]) {
    @targetName("applyFun")
    def apply(a: Expr[A])(using pos: SourcePos, ctx: LambdaContext): Expr[B] =
      Expr.map(a, f)(pos)
  }

  extension [A, B](f: Expr[A --> B]) {
    @targetName("evalFunExpr")
    def apply(a: Expr[A])(using pos: SourcePos, ctx: LambdaContext): Expr[B] =
      Expr.map((f ** a)(using pos), eval)(pos)
  }

  extension [A](self: Expr[Unlimited[A]]) {
    def split(using pos: SourcePos, ctx: LambdaContext): (Expr[Unlimited[A]], Expr[Unlimited[A]]) =
      **.unapply(Unlimited.split[A](self)(using pos))(using pos)

    def get(using pos: SourcePos, ctx: LambdaContext): Expr[A] =
      Expr.map(self, Unlimited.getSingle)(pos)
  }

  given singleOptionPick[K <: String & Singleton, V]: Picked[K of V, K, V]
  given choicePickLeft[A, K <: String & Singleton, V, B](using ev: Picked[A, K, V]): Picked[A |&| B, K, V]
  given choicePickRight[A, B, K <: String & Singleton, V](using ev: Picked[B, K, V]): Picked[A |&| B, K, V]

  given valueTypeText: ValueType[Text]
  given valueTypeFloat64: ValueType[Float64]
  given valueTypeSingleFieldRecord[N <: String & Singleton, T](using ConstValue[N], ValueType[T]): ValueType[Record[N of T]]
  given valueTypeRecord[A, N <: String & Singleton, T](using ValueType[Record[A]], ConstValue[N], ValueType[T]): ValueType[Record[A ### (N of T)]]

  trait Affine[A] {
    def discard: Fun[A, EmptyResource]
  }

  object Affine {
    def from[A](f: Fun[A, EmptyResource]): Affine[A] =
      new Affine[A] {
        override def discard: Fun[A, EmptyResource] =
          f
      }

    given affineEmpty: Affine[EmptyResource] =
      from(id[EmptyResource])

    given affinePair[A, B](using A: Affine[A], B: Affine[B]): Affine[A ** B] =
      from(fun { case a ** b => B.discard(b) alsoElim A.discard(a) })
  }

  trait Cosemigroup[A] {
    def split: Fun[A, A ** A]
  }

  trait Comonoid[A] extends Cosemigroup[A] with Affine[A] {
    def counit: Fun[A, EmptyResource]

    override def discard: Fun[A, EmptyResource] =
      counit
  }

  object Comonoid {
    given Comonoid[EmptyResource] with {
      override def counit: Fun[EmptyResource, EmptyResource] =
        id[EmptyResource]

      override def split: Fun[EmptyResource, EmptyResource ** EmptyResource] =
        fun(_ => Expr.unit ** Expr.unit)
    }
  }
}
