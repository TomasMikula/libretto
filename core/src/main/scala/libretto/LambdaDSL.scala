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
    * @throws UnboundVariablesException if the result expression contains free variables (from outer [[λ]]s).
    */
  def λ[A, B](f: $[A] => $[B])(implicit
    file: sourcecode.File,
    line: sourcecode.Line,
  ): A -⚬ B

  type NotLinearException <: Throwable
  type UnboundVariablesException <: Throwable

  val $: $Ops

  trait $Ops {
    def map[A, B](a: $[A])(f: A -⚬ B)(
      file: String,
      line: Int,
    ): $[B]

    def zip[A, B](a: $[A], b: $[B])(
      file: String,
      line: Int,
    ): $[A |*| B]

    def unzip[A, B](ab: $[A |*| B])(
      file: String,
      line: Int,
    ): ($[A], $[B])

    object |*| {
      def unapply[A, B](ab: $[A |*| B])(implicit
        file: sourcecode.File,
        line: sourcecode.Line,
      ): ($[A], $[B]) =
        unzip(ab)(file.value, line.value)
    }

    extension [A, B](f: A -⚬ B) {
      def apply(a: $[A])(implicit
        file: sourcecode.File,
        line: sourcecode.Line,
      ): $[B] =
        map(a)(f)(file.value, line.value)
    }

    extension [A, B](a: $[A]) {
      def |*|(b: $[B])(implicit
        file: sourcecode.File,
        line: sourcecode.Line,
      ): $[A |*| B] =
        zip(a, b)(file.value, line.value)

      def >(f: A -⚬ B)(implicit
        file: sourcecode.File,
        line: sourcecode.Line,
      ): $[B] =
        map(a)(f)(file.value, line.value)
    }
  }
}
