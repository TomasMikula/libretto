package libretto.typology.toylang.typeinfer

import libretto.scaletto.StarterKit.*
import libretto.typology.toylang.types.Type

trait TypeOps[F[_], V] {
  def map[A, B](f: A -⚬ B): F[A] -⚬ F[B]

  // TODO: eliminate the output parameter
  def merge[A](f: (A |*| A) -⚬ A, output: A -⚬ Val[Type[V]]): (F[A] |*| F[A]) -⚬ F[A]

  def split[A](f: A -⚬ (A |*| A)): F[A] -⚬ (F[A] |*| F[A])

  def output[A](f: A -⚬ Val[Type[V]]): F[A] -⚬ Val[Type[V]]

  def close[A](f: A -⚬ Done): F[A] -⚬ Done

  def awaitPosFst[A](f: (Done |*| A) -⚬ A): (Done |*| F[A]) -⚬ F[A]
}