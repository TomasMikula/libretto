package libretto.util

trait Semigroup[A] {
  def combine(l: A, r: A): A
}
