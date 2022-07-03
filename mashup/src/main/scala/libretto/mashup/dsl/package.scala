package libretto.mashup

import libretto.StarterKit.{dsl => StarterDsl}
import libretto.StarterKit.dsl.{-⚬, =⚬, |*|, |+|, One, Val}
import libretto.scalasource

package object dsl {
  opaque type Fun[A, B] = A -⚬ B // for now, let's just use libretto's linear functions

  opaque type EmptyResource = One

  opaque type or[A, B] = A |+| B

  /** Higher-order function, i.e. one that occurs on input or output of [[Blueprint]]s. */
  opaque type -->[A, B] = A =⚬ B

  opaque type Text = Val[String]

  opaque type Float64 = Val[Double]

  opaque type Expr[A] = StarterDsl.$[A]

  opaque type Record = One

  opaque type ##[A, B] = A |*| B

  opaque type of[Name <: String, T] = T


  def fun[A, B](f: Expr[A] => Expr[B]): Fun[A, B] =
    StarterDsl.λ(f)

  def closure[A, B](f: Expr[A] => Expr[B]): Expr[A --> B] =
    StarterDsl.Λ(f)

  def id[A]: Fun[A, A] =
    StarterDsl.id[A]

  def left[A, B]: Fun[A, A or B] =
    StarterDsl.injectL[A, B]

  def right[A, B]: Fun[B, A or B] =
    StarterDsl.injectR[A, B]

  import StarterDsl.$._

  object Record {
    def apply()(using pos: scalasource.Position): Expr[Record] =
      one(using pos)
  }

  object Float64 {
    def apply(value: Double)(using pos: scalasource.Position): Expr[Float64] =
      one(using pos) > StarterDsl.done > StarterDsl.constVal(value)
  }

  extension [A](a: Expr[A]) {
    def ##[N <: String](using name: ConstValue[N]): RecordExtender[A, N] =
      new RecordExtender(a, name)

    def alsoElim(empty: Expr[EmptyResource])(using
      pos: scalasource.Position,
    ): Expr[A] =
      StarterDsl.$.eliminateSecond(a, empty)(pos)
  }

  class RecordExtender[A, N <: String](initial: Expr[A], fieldName: ConstValue[N]) {
    def apply[T](value: Expr[T])(using
      pos: scalasource.Position,
    ): Expr[A ## (N of T)] =
      StarterDsl.$.zip(initial, value)(pos)
  }
}
