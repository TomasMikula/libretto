package libretto.lambda

import libretto.lambda.util.{Exists, Functional, TypeEq}
import libretto.lambda.util.TypeEq.Refl

trait ArrowMap[-->[_, _], ->>[_, _], F[_, _]] {
  type Image[A, B] = MappedMorphism[->>, F, A, B]

  def map[A, B](f: A --> B): Image[A, B]

  def map[A, B, S](fa: F[A, S], f: A --> B)(using F: Functional[F]): Exists[[T] =>> (S ->> T, F[B, T])] = {
    val g = map(f)
    F.uniqueOutputType(fa, g.srcMap) match
      case TypeEq(Refl()) =>
        Exists((g.ff, g.tgtMap))
  }
}
