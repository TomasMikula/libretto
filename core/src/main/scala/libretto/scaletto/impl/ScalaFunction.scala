package libretto.scaletto.impl

import libretto.util.Async

enum ScalaFunction[A, B] {
  case Direct(f: A => B)
  case Blocking(f: A => B)
  case Asynchronous(f: A => Async[B])
  case Step[A, X, B](f: A => (ScalaFunction[X, B], X)) extends ScalaFunction[A, B]

  def adapt[Z, C](pre: Z => A, post: B => C): ScalaFunction[Z, C] =
    this match {
      case Direct(f)       => Direct(pre andThen f andThen post)
      case Blocking(f)     => Blocking(pre andThen f andThen post)
      case Asynchronous(f) => Asynchronous(z => f(pre(z)).map(post))
      case Step(f)         => Step(z => f(pre(z)) match { case (g, x) => (g.adaptPost(post), x) })
    }

  def adaptPost[C](post: B => C): ScalaFunction[A, C] =
    this match {
      case Direct(f)       => Direct(f andThen post)
      case Blocking(f)     => Blocking(f andThen post)
      case Asynchronous(f) => Asynchronous(a => f(a).map(post))
      case Step(f)         => Step(a => f(a) match { case (g, x) => (g.adaptPost(post), x) })
    }

  def adaptWith[Z, P, C](
    pre: Z => (P, A),
    post: (P, B) => C,
  ): ScalaFunction[Z, C] =
    this match {
      case Direct(f)       => Direct      (z => pre(z) match { case (p, a) => post(p, f(a)) })
      case Blocking(f)     => Blocking    (z => pre(z) match { case (p, a) => post(p, f(a)) })
      case Asynchronous(f) => Asynchronous(z => pre(z) match { case (p, a) => f(a).map(post(p, _)) })
      case Step(f)         => Step        (z => pre(z) match { case (p, a) => val (g, x) = f(a); (g.adaptPost(b => post(p, b)), x) })
    }
}

object ScalaFunction {
  def eval[A, B]: ScalaFunction[(ScalaFunction[A, B], A), B] =
    Step(identity[(ScalaFunction[A, B], A)])
}
