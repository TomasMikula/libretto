package libretto.lambda

import libretto.lambda.util.{Applicative, Monad}

/** A collection of arrows of the form `Ai --> B`, with `A = A1 <+> ... <+> An`. */
sealed trait Sink[-->[_, _], <+>[_, _], A, B] {
  import Sink.*

  def <+>[X](that: Sink[-->, <+>, X, B]): Sink[-->, <+>, A <+> X, B] =
    Join(this, that)

  def map[->>[_, _]](g: [x] => (x --> B) => (x ->> B)): Sink[->>, <+>, A, B] =
    this match {
      case Arrow(f)     => Arrow(g(f))
      case Join(s1, s2) => Join(s1.map(g), s2.map(g))
    }

  def traverse[G[_]: Applicative, ->>[_, _]](
    g: [x] => (x --> B) => G[x ->> B],
  ): G[Sink[->>, <+>, A, B]] =
    this match {
      case Arrow(f)     => g(f).map(Arrow(_))
      case Join(s1, s2) => Applicative[G].map2(s1.traverse(g), s2.traverse(g))(Join(_, _))
    }

  def reduce(
    g: [x, y] => (x --> B, y --> B) => (x <+> y) --> B
  ): A --> B =
    this match {
      case Arrow(f)     => f
      case Join(s1, s2) => g(s1.reduce(g), s2.reduce(g))
    }

  def reduceM[M[_]: Monad](
    g: [x, y] => (x --> B, y --> B) => M[(x <+> y) --> B]
  ): M[A --> B] =
    this match {
      case Arrow(f)     => Monad[M].pure(f)
      case Join(s1, s2) => Monad[M].flatMap2(s1.reduceM(g), s2.reduceM(g))(g(_, _))
    }
}

object Sink {
  case class Arrow[-->[_, _], <+>[_, _], A, B](
    f: A --> B,
  ) extends Sink[-->, <+>, A, B]

  case class Join[-->[_, _], <+>[_, _], A1, A2, B](
    s1: Sink[-->, <+>, A1, B],
    s2: Sink[-->, <+>, A2, B],
  ) extends Sink[-->, <+>, A1 <+> A2, B]

  def apply[-->[_, _], <+>[_, _], A, B](f: A --> B): Sink[-->, <+>, A, B] =
    Arrow(f)

  def apply[-->[_, _], <+>[_, _], A, B, C](
    a: Sink[-->, <+>, A, C],
    b: Sink[-->, <+>, B, C],
  ): Sink[-->, <+>, A <+> B, C] =
    Join(a, b)
}
