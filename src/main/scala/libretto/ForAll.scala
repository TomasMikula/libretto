package libretto

trait ForAll[+F[_]] {
  def apply[A]: F[A]
}
