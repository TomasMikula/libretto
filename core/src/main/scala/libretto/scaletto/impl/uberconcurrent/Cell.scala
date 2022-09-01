package libretto.scaletto.impl.uberconcurrent

sealed trait Cell[A]

object Cell {
  def empty[A]: Cell[A] =
    ??? // TODO
}
