package libretto.exec

import libretto.lambda.Tupled
import libretto.lambda.util.{Exists, TypeEq}
import libretto.lambda.util.TypeEq.Refl

opaque type ExecutionParams[P[_], A] =
  Either[
    A =:= Unit,
    Tupled[Tuple2, P, A]
  ]

object ExecutionParams {
  def unit[P[_]]: ExecutionParams[P, Unit] =
    Left(summon[Unit =:= Unit])

  def wrap[P[_], A](pa: P[A]): ExecutionParams[P, A] =
    Right(Tupled.atom(pa))

  def fromTupled[P[_], A](pa: Tupled[Tuple2, P, A]): ExecutionParams[P, A] =
    Right(pa)

  extension [P[_], A](pa: ExecutionParams[P, A]) {
    def asTupled: Either[A =:= Unit, Tupled[Tuple2, P, A]] =
      pa

    def adapt[Q[_]](
      h: [Y] => P[Y] => Exists[[X] =>> (Q[X], X => Y)]
    ): Exists[[X] =>> (ExecutionParams[Q, X], X => A)] =
      pa match
        case Left(TypeEq(Refl())) =>
          Exists((unit, identity))
        case Right(fa) =>
          fa.foldMapWith[[T] =>> Exists[[X] =>> (Tupled[Tuple2, Q, X], X => T)]](
            [Y] => py =>
              h(py) match {
                case Exists.Some((qx, f)) => Exists((Tupled.atom(qx), f))
              },
            [Y1, Y2] => (y1, y2) =>
              (y1, y2) match {
                case (Exists.Some((qx1, f1)), Exists.Some((qx2, f2))) =>
                  Exists((qx1 zip qx2), (x1, x2) => (f1(x1), f2(x2)))
              },
          ) match
            case Exists.Some((qa, f)) => Exists((Right(qa), f))
  }
}
