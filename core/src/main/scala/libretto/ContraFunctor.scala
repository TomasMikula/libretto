package libretto

/** Witnesses that `F` is a contravariant endofunctor on the category `->`. */
trait ContraFunctor[->[_, _], F[_]] { self =>
  def lift[A, B](f: A -> B): F[B] -> F[A]

  /** Composition with a covariant functor. Results in a contravariant functor. */
  def ∘[G[_]](that: Functor[->, G]): ContraFunctor[->, λ[x => F[G[x]]]] =
    new ContraFunctor[->, λ[x => F[G[x]]]] {
      def lift[A, B](f: A -> B): F[G[B]] -> F[G[A]] =
        self.lift(that.lift(f))
    }

  /** Composition with another contravariant functor. Results in a covariant functor. */
  def ∘[G[_]](that: ContraFunctor[->, G]): Functor[->, λ[x => F[G[x]]]] =
    new Functor[->, λ[x => F[G[x]]]] {
      def lift[A, B](f: A -> B): F[G[A]] -> F[G[B]] =
        self.lift(that.lift(f))
    }
}

object ContraFunctor {
  def apply[->[_, _], F[_]](using ev: ContraFunctor[->, F]): ContraFunctor[->, F] =
    ev
}
