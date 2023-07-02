package libretto

import libretto.lambda.Category

/** Witnesses that `F` is a bifunctor (covariant in both variables) on the category `->`. */
trait Bifunctor[->[_, _], F[_, _]] { self =>
  val category: Category[->]

  def lift[A, B, C, D](f: A -> B, g: C -> D): F[A, C] -> F[B, D]

  def fst[B]: Functor[->, F[*, B]] =
    new Functor[->, F[*, B]] {
      override val category =
        self.category

      override def lift[A1, A2](f: A1 -> A2): F[A1, B] -> F[A2, B] =
        Bifunctor.this.lift[A1, A2, B, B](f, this.category.id[B])
    }

  def snd[A]: Functor[->, F[A, *]] =
    new Functor[->, F[A, *]] {
      override val category =
        self.category

      override def lift[B1, B2](g: B1 -> B2): F[A, B1] -> F[A, B2] =
        Bifunctor.this.lift[A, A, B1, B2](this.category.id[A], g)
    }

  def inside[G[_]](using G: Functor[->, G]): Bifunctor[->, λ[(x, y) => G[F[x, y]]]] =
    new Bifunctor[->, λ[(x, y) => G[F[x, y]]]] {
      override val category =
        self.category

      override def lift[A, B, C, D](f: A -> B, g: C -> D): G[F[A, C]] -> G[F[B, D]] =
        G.lift(Bifunctor.this.lift(f, g))
    }
}

object Bifunctor {
  def apply[->[_, _], F[_, _]](using ev: Bifunctor[->, F]): Bifunctor[->, F] =
    ev
}
