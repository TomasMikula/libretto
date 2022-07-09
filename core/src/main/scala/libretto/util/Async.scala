package libretto.util

import scala.concurrent.{ExecutionContext, Future, Promise}
import scala.util.{Failure, Success, Try}

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

  def never[A]: Async[A] =
    Later(_ => ())

  def fromFuture[A](fa: Future[A]): Async[Try[A]] =
    fa.value match {
      case Some(ta) => Now(ta)
      case None => Later(callback => fa.onComplete(callback)(ExecutionContext.parasitic))
    }

  /** If the future fails, the returned `Async` never completes and the `onError` callback is invoked. */
  def unsafeFromFuture[A](fa: Future[A], onError: Throwable => Unit): Async[A] =
    fa.value match {
      case Some(ta) =>
        ta match {
          case Success(a) => Now(a)
          case Failure(e) => onError(e); never
        }
      case None =>
        Later(callback => fa.onComplete {
          case Success(a) => callback(a)
          case Failure(e) => onError(e)
        }(ExecutionContext.parasitic))
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
