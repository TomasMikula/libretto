package libretto.exec

trait Execution[DSL <: { type -⚬[A, B] }] {
  val dsl: DSL
  import dsl.-⚬

  type InPort[A]
  val InPort: InPorts

  type OutPort[A]
  val OutPort: OutPorts

  trait InPorts {
    def contramap[A, B](port: InPort[B])(f: A -⚬ B): InPort[A]
  }

  trait OutPorts {
    def map[A, B](port: OutPort[A])(f: A -⚬ B): OutPort[B]
  }
}
