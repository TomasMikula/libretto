package libretto

import scala.annotation.targetName

trait LambdaDSL extends CoreDSL {
  /** The type of auxiliary placeholder variables used e.g. as arguments to [[λ]]. */
  type $[A]

  /** Used to define a linear function `A -⚬ B` in a point-full style, i.e. as a lambda expression.
    *
    * Recall that when defining `A -⚬ B`, we never get a hold of `a: A` as a Scala value. However,
    * by using this method we get a hold of `a: $[A]`, a placeholder variable, and construct the result
    * expression `$[B]`.
    * This method then inspects how the input variable `a: $[A]` is used in the result `$[B]` and
    * infers a (point-free) construction of `A -⚬ B`.
    *
    * @throws NotLinearException if the given function violates linearity, i.e. if the input variable
    *   is not used exactly once.
    * @throws UnboundVariableException if the result expression contains free variables (from outer [[λ]]s).
    */
  def λ[A, B](f: $[A] => $[B]): A -⚬ B

  type NotLinearException <: Throwable
  type UnboundVariableException <: Throwable

  val $: $Ops

  trait $Ops {
    def zip[A, B](a: $[A], b: $[B]): $[A |*| B]

    def unzip[A, B](ab: $[A |*| B]): ($[A], $[B])

    object |*| {
      def unapply[A, B](ab: $[A |*| B]): ($[A], $[B]) =
        unzip(ab)
    }

    extension [A, B](f: A -⚬ B) {
      def apply(a: $[A]): $[B] =
        $.map(a)(f)
    }

    extension [A, B](a: $[A]) {
      def |*|(b: $[B]): $[A |*| B] =
        $.zip(a, b)
    }
  }
}
