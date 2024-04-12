package libretto.lambda

import scala.annotation.targetName

trait Zippable[|*|[_, _], F[_]] { self =>
  def zip[A, B](fa: F[A], fb: F[B]): F[A |*| B]

  extension [A](fa: F[A])
    @targetName("zip_ext")
    infix def zip[B](fb: F[B]): F[A |*| B] =
      self.zip(fa, fb)
}
