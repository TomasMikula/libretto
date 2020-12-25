package libretto

trait ForAll[+F[_]] {
  def apply[A]: F[A]
}

trait ForAll2[+F[_, _]] { self =>
  def apply[A, B]: F[A, B]
  
  def flipTArgs: ForAll2[[x, y] =>> F[y, x]] =
    new ForAll2[[x, y] =>> F[y, x]] {
      override def apply[A, B]: F[B, A] = self.apply[B, A]
    }
}
