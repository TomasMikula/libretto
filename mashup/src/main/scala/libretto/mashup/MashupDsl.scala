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

  type Record

  type ##[A, B]

  type NamedChoice[Options]

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
    def apply()(using pos: scalasource.Position): Expr[Record]
  }

  val Float64: Float64s

  trait Float64s {
    def apply(value: Double)(using pos: scalasource.Position): Expr[Float64]
  }

  val Expr: Exprs

  trait Exprs {
    def eliminateSecond[A](a: Expr[A], empty: Expr[EmptyResource])(pos: scalasource.Position): Expr[A]

    def extendRecord[A, N <: String, T](init: Expr[A], last: (N, Expr[T]))(pos: scalasource.Position): Expr[A ## (N of T)]
  }

  val Unlimited: Unlimiteds

  trait Unlimiteds {
    def map[A, B](f: Fun[A, B]): Fun[Unlimited[A], Unlimited[B]]
  }

  extension [A](a: Expr[A]) {
    def ##[N <: String](using name: ConstValue[N]): RecordExtender[A, N] =
      new RecordExtender(a, name)

    def alsoElim(empty: Expr[EmptyResource])(using
      pos: scalasource.Position,
    ): Expr[A] =
      Expr.eliminateSecond(a, empty)(pos)
  }

  class RecordExtender[A, N <: String](initial: Expr[A], fieldName: ConstValue[N]) {
    def apply[T](value: Expr[T])(using
      pos: scalasource.Position,
    ): Expr[A ## (N of T)] =
      Expr.extendRecord[A, N, T](initial, (fieldName.value, value))(pos)
  }
}
