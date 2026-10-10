package libretto.lambda

trait Category[->[_, _]] extends NarrowCategory[[x] =>> Unit, ->] with Semigroupoid[->] {
  def id[A]: A -> A

  override def id[A](using witness: Unit): A -> A = id[A]
}
