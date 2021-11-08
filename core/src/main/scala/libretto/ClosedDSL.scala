package libretto

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

  /** Creates a closure (`A =⚬ B`), i.e. a function that captures variables from the outer scope,
    * as an expression (`$[A =⚬ B]`) that can be used in outer [[λ]] or [[Λ]].
    */
  def Λ[A, B](f: $[A] => $[B])(implicit
    file: sourcecode.File,
    line: sourcecode.Line,
  ): $[A =⚬ B]

  type NoCaptureException <: Throwable

  trait ClosureOps extends $Ops {
    def app[A, B](f: $[A =⚬ B], a: $[A])(
      file: String,
      line: Int,
    ): $[B]

    implicit class ClosureOps[A, B](f: $[A =⚬ B]) {
      def apply(a: $[A])(implicit
        file: sourcecode.File,
        line: sourcecode.Line,
      ): $[B] =
        app(f, a)(file.value, line.value)
    }
  }

  override val $: ClosureOps
}
