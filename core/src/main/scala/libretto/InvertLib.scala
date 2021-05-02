package libretto

object InvertLib {
  def apply(
    coreLib: CoreLib[_ <: InvertDSL],
  ): InvertLib[coreLib.type] =
    new InvertLib[coreLib.type](coreLib)
}

class InvertLib[
  CoreLib <: libretto.CoreLib[_ <: InvertDSL],
](
  val coreLib: CoreLib,
) {
  import coreLib.dsl._
  import coreLib._

  def pool[A: Signaling.Positive]: LList1[A] -⚬ (Unlimited[A |*| -[A]] |*| LList1[A]) =
    coreLib.pool[A, -[A]](forevert[A])
}
