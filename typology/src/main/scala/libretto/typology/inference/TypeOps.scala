package libretto.typology.inference

import libretto.scaletto.StarterKit.*

trait TypeOps[F[_], T, V] {
  def map[A, B]: Sub[A, B] -⚬ (F[A] =⚬ F[B])

  def mapWith[X, A, B](using
    CloseableCosemigroup[X],
  ): Sub[X |*| A, B] -⚬ ((X |*| F[A]) =⚬ F[B])

  def merge[A]: Sub[A |*| A, A] -⚬ ((F[A] |*| F[A]) =⚬ F[A])

  def split[A]: Sub[A, A |*| A] -⚬ (F[A] =⚬ (F[A] |*| F[A]))

  def output[A]: Sub[A, Val[T]] -⚬ (F[A] =⚬ Val[T])

  def close[A]: Sub[A, Done] -⚬ (F[A] =⚬ Done)

  /** Forbidden self reference involving the given inference variable [[V]]. */
  def forbiddenSelfReference[A]: Val[V] -⚬ F[A]

  def awaitPosFst[A]: Sub[Done |*| A, A] -⚬ ((Done |*| F[A]) =⚬ F[A])
}