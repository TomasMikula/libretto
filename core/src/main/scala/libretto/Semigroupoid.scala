package libretto

trait Semigroupoid[->[_, _]] {
  def andThen[A, B, C](f: A -> B, g: B -> C): A -> C

  extension [A, B, C](f: A -> B) {
    def >(g: B -> C): A -> C =
      andThen(f, g)
  }
}
