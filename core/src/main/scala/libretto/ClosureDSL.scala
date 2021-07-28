package libretto

trait ClosureDSL extends ClosedDSL with LambdaDSL {
  def Λ[A, B](f: $[A] => $[B]): $[A =⚬ B]

  type NoCaptureException <: Throwable

  trait ClosureOps extends $Ops {
    def app[A, B](f: $[A =⚬ B], a: $[A]): $[B]

    implicit class ClosureOps[A, B](f: $[A =⚬ B]) {
      def apply(a: $[A]): $[B] =
        app(f, a)
    }
  }

  override val $: ClosureOps
}
