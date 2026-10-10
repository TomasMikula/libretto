package libretto.lambda

trait Semigroupoid[->[_, _]] extends NarrowSemigroupoid[[x] =>> Unit, ->] {
  def andThen[A, B, C](f: A -> B, g: B -> C): A -> C

  override def narrowAndThen[A, B, C](f: A -> B, g: B -> C)(using a: Unit, b: Unit, c: Unit): A -> C =
    andThen(f, g)

  extension [A, B](f: A -> B) {
    def >[C](g: B -> C): A -> C =
      andThen(f, g)

    def to[C](using B =:= C): A -> C =
      summon[B =:= C].substituteCo(f)

    def from[Z](using Z =:= A): Z -> B =
      summon[Z =:= A].substituteContra[[a] =>> a -> B](f)
  }
}
