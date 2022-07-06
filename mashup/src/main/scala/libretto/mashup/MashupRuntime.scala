package libretto.mashup

trait MashupRuntime[DSL <: MashupDsl] {
  val dsl: DSL

  type InPort[A]
  type OutPort[A]
  type Execution

  import dsl.Fun

  def run[A, B](f: Fun[A, B]): (InPort[A], OutPort[B], Execution)
}
