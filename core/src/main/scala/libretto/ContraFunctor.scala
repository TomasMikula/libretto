package libretto

import libretto.lambda.Category

/** Witnesses that `F` is a contravariant endofunctor on the category `->`. */
trait ContraFunctor[->[_, _], F[_]] { self =>
  val category: Category[->]

  def lift[A, B](f: A -> B): F[B] -> F[A]

  /** Composition with a covariant functor. Results in a contravariant functor. */
  def ∘[G[_]](that: Functor[->, G]): ContraFunctor[->, [x] =>> F[G[x]]] =
    new ContraFunctor[->, [x] =>> F[G[x]]] {
      override val category =
        self.category

      override def lift[A, B](f: A -> B): F[G[B]] -> F[G[A]] =
        self.lift(that.lift(f))
    }

  /** Composition with another contravariant functor. Results in a covariant functor. */
  def ∘[G[_]](that: ContraFunctor[->, G]): Functor[->, [x] =>> F[G[x]]] =
    new Functor[->, [x] =>> F[G[x]]] {
      override val category =
        self.category

      override def lift[A, B](f: A -> B): F[G[A]] -> F[G[B]] =
        self.lift(that.lift(f))
    }
}

object ContraFunctor {
  def apply[->[_, _], F[_]](using ev: ContraFunctor[->, F]): ContraFunctor[->, F] =
    ev
}
