package libretto.scaletto.impl

trait Monoid[M] {
  def unit: M
  def combine(m: M, n: M): M

  extension (m: M) {
    def <>(n: M): M = combine(m, n)
  }
}
