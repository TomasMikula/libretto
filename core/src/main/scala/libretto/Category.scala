package libretto

trait Category[->[_, _]] extends Semigroupoid[->] {
  def id[A]: A -> A
}
