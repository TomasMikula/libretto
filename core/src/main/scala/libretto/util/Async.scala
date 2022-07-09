package libretto.util

import java.util.concurrent.atomic.AtomicReference
import java.util.function.BinaryOperator
import scala.concurrent.{Await, ExecutionContext, Future, Promise}
import scala.concurrent.duration.Duration
import scala.util.{Failure, Success, Try}

sealed trait Async[A] {
  def map[B](f: A => B): Async[B] =
    this match {
      case Async.Now(a) => Async.Now(f(a))
      case Async.Later(register) => Async.Later(onB => register(f andThen onB))
    }

  def flatMap[B](f: A => Async[B]): Async[B] =
    this match {
      case Async.Now(a) => f(a)
      case Async.Later(register) =>
        Async.Later(onB => register(a => f(a).onComplete(onB)))
    }

  def onComplete(callback: A => Unit): Unit =
    this match {
      case Async.Now(a)          => callback(a)
      case Async.Later(register) => register(callback)
    }
}

object Async {
  case class Now[A](value: A) extends Async[A]
  case class Later[A](register: (A => Unit) => Unit) extends Async[A]

  def now[A](value: A): Async[A] =
    Now(value)

  def later[A](register: (A => Unit) => Unit): Async[A] =
    Later(register)

  def defer[A](a: => A): Async[A] =
    later(f => f(a))

  def never[A]: Async[A] =
    Later(_ => ())

  /** Returns an `Async[A]` value and a completer function that will complete it.
    * The returned completer function must be called exactly once. An exception will
    * be thrown on subsequent calls.
    * The returned `Async` must register a listener exactly once. An exception will
    * be thrown on subsequent listeners.
    */
  def promise[A]: (A => Unit, Async[A]) = {
    enum State[A] {
      case Initial()
      case Value(value: A)
      case Listener(listener: A => Unit)
      case Done()
    }
    import State._

    val ref =
      new AtomicReference[State[A]](State.Initial())
    val stateUpdate: BinaryOperator[State[A]] =
      { (oldState, newState) =>
        (oldState, newState) match {
          case (Initial()     , l: Listener[A]    ) => l
          case (Initial()     , v: Value[A]       ) => v
          case (_: Listener[A], _: Value[A]       ) => Done()
          case (_: Value[A]   , _: Listener[A]    ) => Done()
          case (l: Listener[A], _: Listener[A]    ) => l
          case (v: Value[A]   , _: Value[A]       ) => v
          case (_             , Initial() | Done()) => throw new AssertionError("We never update by Initial or Done")
          case (d @ Done()    , _                 ) => d
        }
      }
    val completer =
      { (a: A) =>
        val oldState = ref.getAndAccumulate(Value(a), stateUpdate)
        oldState match {
          case Initial()          => // do nothing
          case Listener(listener) => listener(a)
          case Value(_) | Done()  => throw new IllegalStateException("Double completion")
        }
      }
    val register =
      { (listener: A => Unit) =>
        val oldState = ref.getAndAccumulate(Listener(listener), stateUpdate)
        oldState match {
          case Initial()            => // do nothing
          case Value(a)             => listener(a)
          case Listener(_) | Done() => throw new IllegalStateException("Double listener registration")
        }
      }
    (completer, Later(register))
  }

  def fromFuture[A](fa: Future[A]): Async[Try[A]] =
    fa.value match {
      case Some(ta) => Now(ta)
      case None => Later(callback => fa.onComplete(callback)(ExecutionContext.parasitic))
    }

  def toFuture[A](async: Async[A]): Future[A] =
    async match {
      case Now(value) => Future.successful(value)
      case Later(register) =>
        val pa = Promise[A]()
        register(pa.success)
        pa.future
    }

  def await[A](a: Async[A]): A =
    Await.result(toFuture(a), Duration.Inf)
}
