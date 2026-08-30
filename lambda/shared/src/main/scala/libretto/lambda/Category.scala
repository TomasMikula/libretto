package libretto.lambda

trait Category[->[_, _]] extends NarrowCategory[[x] =>> Unit, ->] {
  def id[A]: A -> A

  override def id[A](witness: Unit): A -> A = id[A]
}
