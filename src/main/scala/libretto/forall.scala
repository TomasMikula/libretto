package libretto

trait ForAll[+F[_]] {
  def apply[A]: F[A]
}

trait ForAll2[+F[_, _]] {
  def apply[A, B]: F[A, B]
}
