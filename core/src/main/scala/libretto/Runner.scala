package libretto

import scala.concurrent.Future

trait Runner[DSL <: CoreDSL] {
  val dsl: DSL

  import dsl._

  def run(prg: Done -⚬ Done): Future[Unit]
}
