package libretto

import libretto.lambda.util.SourcePos

/** Extension of [[CoreDSL]] that adds support for "functions as data" (`=⚬`).
  * In other words, it makes [[CoreDSL.-⚬]] a ''closed'' monoidal category.
  */
trait ClosedDSL extends CoreDSL {
  /** Linear function as data, that is, one that can be part of an input or output of a linear function (`-⚬`).
    * While `A -⚬ B` is a morphism in a category, `A =⚬ B` is an object called the internal hom of `A` and `B`
    * in a closed monoidal category.
    */
  type =⚬[A, B]

  def curry[A, B, C](f: (A |*| B) -⚬ C): A -⚬ (B =⚬ C)

  def eval[A, B]: ((A =⚬ B) |*| A) -⚬ B

  def uncurry[A, B, C](f: A -⚬ (B =⚬ C)): (A |*| B) -⚬ C =
    andThen(par(f, id[B]), eval[B, C])

  /** Turn a function into a function object. */
  def obj[A, B](f: A -⚬ B): One -⚬ (A =⚬ B) =
    curry(andThen(elimFst, f))

  /** Map the output of a function object. */
  def out[A, B, C](f: B -⚬ C): (A =⚬ B) -⚬ (A =⚬ C) =
    curry(andThen(eval[A, B], f))

  override val λ: LambdaOpsWithClosures

  trait LambdaOpsWithClosures extends LambdaOps {
    val closure: ClosureOps
  }

  trait ClosureOps {
    /** Creates a closure (`A =⚬ B`), i.e. a function that captures variables from the outer scope,
      * as an expression (`$[A =⚬ B]`) that can be used in outer [[λ]].
      */
    def apply[A, B](using SourcePos, LambdaContext)(
      f: LambdaContext ?=> $[A] => $[B],
    ): $[A =⚬ B]

    def ?[A, B](using SourcePos, LambdaContext)(
      f: LambdaContext ?=> $[A] => $[B],
    )(using
      Affine[A],
    ): $[A =⚬ B] =
      apply { case ?(a) => f(a) }

    def +[A, B](using SourcePos, LambdaContext)(
      f: LambdaContext ?=> $[A] => $[B],
    )(using
      Cosemigroup[A],
    ): $[A =⚬ B] =
      apply { case +(a) => f(a) }

    def *[A, B](using SourcePos, LambdaContext)(
      f: LambdaContext ?=> $[A] => $[B],
    )(using
      Comonoid[A],
    ): $[A =⚬ B] =
      apply { case *(a) => f(a) }
  }

  /** Alias for [[λ.closure.apply]]. */
  @deprecated("Use λ.closure instead.", since = "0.2")
  def Λ[A, B](using SourcePos, LambdaContext)(
    f: $[A] => $[B],
  ): $[A =⚬ B] =
    λ.closure(f)

  type NoCaptureException <: Throwable

  trait FunExprOps extends $Ops {
    def app[A, B](f: $[A =⚬ B], a: $[A])(
      pos: SourcePos,
    )(using
      LambdaContext,
    ): $[B]

    implicit class ClosureOps[A, B](f: $[A =⚬ B]) {
      def apply(a: $[A])(using
        pos: SourcePos,
        ctx: LambdaContext,
      ): $[B] =
        app(f, a)(pos)
    }
  }

  override val $: FunExprOps
}
