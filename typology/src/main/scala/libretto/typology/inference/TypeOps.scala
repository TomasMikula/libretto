package libretto.typology.inference

import libretto.scaletto.StarterKit.*

trait TypeOps[F[_], T, V] {
  def map[A, B](f: A -⚬ B): F[A] -⚬ F[B]

  def mapWith[X, A, B](f: (X |*| A) -⚬ B)(using
    CloseableCosemigroup[X],
  ): (X |*| F[A]) -⚬ F[B]

  def merge[A](f: (A |*| A) -⚬ A): (F[A] |*| F[A]) -⚬ F[A]

  def split[A](f: A -⚬ (A |*| A)): F[A] -⚬ (F[A] |*| F[A])

  def output[A](f: A -⚬ Val[T]): F[A] -⚬ Val[T]

  def close[A](f: A -⚬ Done): F[A] -⚬ Done

  /** Forbidden self reference involving the given inference variable [[V]]. */
  def forbiddenSelfReference[A]: Val[V] -⚬ F[A]

  def awaitPosFst[A](f: (Done |*| A) -⚬ A): (Done |*| F[A]) -⚬ F[A]
}