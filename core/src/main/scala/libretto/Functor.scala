package libretto

/** Witnesses that `F` is a covariant endofunctor on the category `->`. */
trait Functor[->[_, _], F[_]] { self =>
  def lift[A, B](f: A -> B): F[A] -> F[B]

  /** Composition with another covariant functor. */
  def ∘[G[_]](that: Functor[->, G]): Functor[->, λ[x => F[G[x]]]] =
    new Functor[->, λ[x => F[G[x]]]] {
      def lift[A, B](f: A -> B): F[G[A]] -> F[G[B]] =
        self.lift(that.lift(f))
    }

  /** Composition with a contravariant functor. Results in a contravariant functor. */
  def ∘[G[_]](that: ContraFunctor[->, G]): ContraFunctor[->, λ[x => F[G[x]]]] =
    new ContraFunctor[->, λ[x => F[G[x]]]] {
      def lift[A, B](f: A -> B): F[G[B]] -> F[G[A]] =
        self.lift(that.lift(f))
    }
}

object Functor {
  def apply[->[_, _], F[_]](using ev: Functor[->, F]): Functor[->, F] =
    ev
}
