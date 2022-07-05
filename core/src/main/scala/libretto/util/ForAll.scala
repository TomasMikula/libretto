package libretto.util

trait ForAll[+F[_]] {
  def apply[A]: F[A]
}
