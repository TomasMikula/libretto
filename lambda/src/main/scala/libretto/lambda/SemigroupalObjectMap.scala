package libretto.lambda

import libretto.lambda.util.Functional

/**
  *
  * @tparam |*| monoidal product in the source "category"
  * @tparam <*> monoidal product in the target "category"
  * @tparam F mapping on objects.
  *   `f: F[A, X]` means that object `A` of the source "category"
  *   is mapped to object `X` in the target "category".
  */
trait SemigroupalObjectMap[|*|[_, _], <*>[_, _], F[_, _]] extends Functional[F] {
  sealed trait Unpaired[A1, A2, X] {
    type X1
    type X2
    val f1: F[A1, X1]
    val f2: F[A2, X2]
    def ev: X =:= (X1 <*> X2)
  }

  object Unpaired {
    case class Impl[A1, A2, T1, T2](override val f1: F[A1, T1], override val f2: F[A2, T2]) extends Unpaired[A1, A2, T1 <*> T2] {
      override type X1 = T1
      override type X2 = T2
      override def ev = summon[(T1 <*> T2) =:= (X1 <*> X2)]
    }
  }

  def pair[A1, A2, X1, X2](f1: F[A1, X1], f2: F[A2, X2]): F[A1 |*| A2, X1 <*> X2]
  def unpair[A1, A2, X](f: F[A1 |*| A2, X]): Unpaired[A1, A2, X]
}
