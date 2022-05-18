package libretto

import scala.concurrent.{ExecutionContext, Future, Promise}
import scala.util.Try

sealed trait Async[A] {
  def map[B](f: A => B): Async[B] =
    this match {
      case Async.Now(a) => Async.Now(f(a))
      case Async.Later(onComplete) => Async.Later(callbackB => onComplete(f andThen callbackB))
    }
}

object Async {
  case class Now[A](value: A) extends Async[A]
  case class Later[A](onComplete: (A => Unit) => Unit) extends Async[A]

  def now[A](value: A): Async[A] =
    Now(value)

  def later[A](onComplete: (A => Unit) => Unit): Async[A] =
    Later(onComplete)

  def defer[A](a: => A): Async[A] =
    later(f => f(a))

  def fromFuture[A](fa: Future[A]): Async[Try[A]] =
    fa.value match {
      case Some(ta) => Now(ta)
      case None => Later(callback => fa.onComplete(callback)(ExecutionContext.parasitic))
    }

  def toFuture[A](async: Async[A]): Future[A] =
    async match {
      case Now(value) => Future.successful(value)
      case Later(onComplete) =>
        val pa = Promise[A]()
        onComplete(pa.success)
        pa.future
    }
}
