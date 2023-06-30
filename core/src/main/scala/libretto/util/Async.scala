package libretto.util

import java.util.concurrent.TimeoutException
import java.util.concurrent.atomic.{AtomicInteger, AtomicReference}
import java.util.function.BinaryOperator
import libretto.util.atomic.*
import scala.annotation.tailrec
import scala.concurrent.{Await, ExecutionContext, Future, Promise}
import scala.concurrent.duration.FiniteDuration
import scala.util.{Failure, Success, Try}

sealed trait Async[+A] {
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

  def zipWith[A, B, C](a: Async[A], b: Async[B])(f: (A, B) => C): Async[C] =
    a.flatMap { a => b.map { b => f(a, b) } }

  def executeOn[A](ec: ExecutionContext)(a: => A): Async[A] = {
    val (complete, aa) = Async.promise[A]
    ec.execute(() => complete(a))
    aa
  }

  /** Returns an `Async[A]` value and a completer function that will complete it.
    * The returned completer function must be called exactly once. An exception will
    * be thrown on subsequent calls.
    * The returned `Async` must register a listener exactly once. An exception will
    * be thrown on subsequent listeners.
    */
  def promiseLinear[A]: (A => Unit, Async[A]) = {
    enum State[A] {
      case Initial()
      case Value(value: A)
      case Listener(listener: A => Unit)
      case Done()
    }
    import State.*

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
          case Listener(listener) => safeInvoke(listener, a)
          case Value(_) | Done()  => throw new IllegalStateException("Double completion")
        }
      }
    val registrar =
      { (listener: A => Unit) =>
        val oldState = ref.getAndAccumulate(Listener(listener), stateUpdate)
        oldState match {
          case Initial()            => // do nothing
          case Value(a)             => listener(a) // don't guard, propagate any error to the provider of listener
          case Listener(_) | Done() => throw new IllegalStateException("Double listener registration")
        }
      }
    (completer, Later(registrar))
  }

  /** Returns an `Async[A]` value and a completer function that will complete it.
    * If the returned completer function is called more than once, the subsequent
    * calls have no effect and return `false`.
    * The returned `Async` can register multiple listeners.
    */
  def promise[A]: (A => Boolean, Async[A]) = {
    sealed trait State[A]
    object State {
      case class Initial[A]() extends State[A]
      case class Value[A](value: A) extends State[A]

      sealed trait Listening[A] extends State[A] {
        @tailrec final def supplyAll(a: A): Unit =
          this match {
            case SingleListener(listener) =>
              safeInvoke(listener, a)
            case Listeners(h, t) =>
              safeInvoke(h, a)
              t.supplyAll(a)
          }
      }
      case class SingleListener(listener: A => Unit) extends Listening[A]
      case class Listeners[A](head: A => Unit, tail: Listening[A]) extends Listening[A]
    }
    import State.*

    val ref =
      new AtomicReference[State[A]](State.Initial())
    val complete: (State[A], A) => (State[A], State[A]) =
      { (state, a) =>
        state match {
          case Initial()       => (Value(a), state)
          case v @ Value(_)    => (v, state)
          case l: Listening[A] => (Value(a), l)
        }
      }
    val register: (State[A], A => Unit) => (State[A], Value[A] | Null) =
      { (state, listener) =>
        state match {
          case Initial()        => (SingleListener(listener), null)
          case ls: Listening[A] => (Listeners(listener, ls), null)
          case v: Value[A]      => (v, v)
        }
      }
    val completer =
      { (a: A) =>
        val oldState = ref.modifyOpaqueWith(a, complete)
        oldState match {
          case Initial()       => true
          case Value(_)        => false
          case l: Listening[A] => l.supplyAll(a); true
        }
      }
    val registrar =
      { (listener: A => Unit) =>
        ref.modifyOpaqueWith(listener, register) match {
          case Value(a) => listener(a) // don't guard, propagate any error to the provider of listener
          case null     => // do nothing
        }
      }
    (completer, Later(registrar))
  }

  private def safeInvoke[A](listener: A => Unit, value: A): Unit =
    try {
      listener(value)
    } catch {
      case _ => // do nothing
    }

  def race[A, B](a: Async[A], b: Async[B]): Async[Either[A, B]] = {
    val (completer, res) = promise[Either[A, B]]
    a.onComplete(a => completer(Left(a)))
    b.onComplete(b => completer(Right(b)))
    res
  }

  def race_[A](a1: Async[A], a2: Async[A]): Async[A] =
    race(a1, a2).map(_.fold(identity, identity))

  def awaitAll(as: Seq[Async[?]]): Async[Unit] = {
    val (complete, promised) = promise[Unit]
    val countdownVar = new AtomicInteger(as.size)
    val listener: Any => Unit = once { _ =>
      val m = countdownVar.decrementAndGet()
      if (m == 0) {
        complete(())
      }
    }
    as.foreach(_.onComplete(listener))
    promised
  }

  private def once[A, B](f: A => B): A => B =
    limitInvocations(f, 1)

  private def limitInvocations[A, B](f: A => B, limit: Int): A => B =
    new Function1[A, B] {
      val remaining = new AtomicInteger(limit)
      override def apply(a: A): B =
        if (remaining.decrementAndGet() >= 0) {
          f(a)
        } else {
          throw new IllegalStateException("The function may not be invoked multiple times")
        }
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

  def await[A](timeout: FiniteDuration)(a: Async[A]): Option[A] =
    try {
      Some(Await.result(toFuture(a), timeout))
    } catch {
      case e: TimeoutException => None
    }
}
