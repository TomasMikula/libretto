package libretto.typology.toylang.typeinfer

import libretto.scaletto.StarterKit.*

trait TypeOps[F[_], T] {
  def map[A, B](f: A -⚬ B): F[A] -⚬ F[B]

  // TODO: eliminate the output parameter
  def merge[A](f: (A |*| A) -⚬ A, output: A -⚬ Val[T]): (F[A] |*| F[A]) -⚬ F[A]

  def split[A](f: A -⚬ (A |*| A)): F[A] -⚬ (F[A] |*| F[A])

  def output[A](f: A -⚬ Val[T]): F[A] -⚬ Val[T]

  def close[A](f: A -⚬ Done): F[A] -⚬ Done

  def awaitPosFst[A](f: (Done |*| A) -⚬ A): (Done |*| F[A]) -⚬ F[A]
}