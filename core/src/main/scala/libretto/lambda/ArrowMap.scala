package libretto.lambda

import libretto.util.{Exists, Functional, TypeEq}
import libretto.util.TypeEq.Refl

trait ArrowMap[-->[_, _], ->>[_, _], F[_, _]] {
  sealed trait Image[A, B] {
    type A1
    type B1
    val srcMap: F[A, A1]
    val tgtMap: F[B, B1]
    val f: A1 ->> B1
  }

  object Image {
    def apply[X, Y, X1, Y1](fx: F[X, X1], ff: X1 ->> Y1, fy: F[Y, Y1]): Image[X, Y] =
      new Image[X, Y] {
        override type A1 = X1
        override type B1 = Y1
        override val srcMap: F[X, X1] = fx
        override val tgtMap: F[Y, Y1] = fy
        override val f: X1 ->> Y1 = ff
      }
  }

  def map[A, B](f: A --> B): Image[A, B]

  def map[A, B, S](fa: F[A, S], f: A --> B)(using F: Functional[F]): Exists[[T] =>> (S ->> T, F[B, T])] = {
    val g = map(f)
    F.uniqueOutputType(fa, g.srcMap) match
      case TypeEq(Refl()) =>
        Exists((g.f, g.tgtMap))
  }
}
