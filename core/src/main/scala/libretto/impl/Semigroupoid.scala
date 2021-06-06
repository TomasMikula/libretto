package libretto.impl

trait Semigroupoid[->[_, _]] {
  def andThen[A, B, C](f: A -> B, g: B -> C): A -> C
}
