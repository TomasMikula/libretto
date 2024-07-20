package libretto

trait ExecutionParams[P[_]] {
  def unit: P[Unit]
  def pair[A, B](a: P[A], b: P[B]): P[(A, B)]
}

object ExecutionParams {
  sealed trait Free[Q[_], A]
  object Free {
    case class One[Q[_]]() extends Free[Q, Unit]
    case class Zip[Q[_], A, B](a: Free[Q, A], b: Free[Q, B]) extends Free[Q, (A, B)]
    case class Ext[Q[_], A](value: Q[A]) extends Free[Q, A]

    def unit[Q[_]]: Free[Q, Unit] =
      One()

    def pair[Q[_], A, B](a: Free[Q, A], b: Free[Q, B]): Free[Q, (A, B)] =
      Zip(a, b)

    def wrap[Q[_], A](qa: Q[A]): Free[Q, A] =
      Ext(qa)
  }
}
