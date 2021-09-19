package libretto

trait ClosureDSL extends ClosedDSL with LambdaDSL {
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
