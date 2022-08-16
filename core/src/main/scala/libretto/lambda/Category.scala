package libretto.lambda

trait Category[->[_, _]] extends Semigroupoid[->] {
  def id[A]: A -> A
}
