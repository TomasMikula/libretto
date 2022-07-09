package libretto.testing

import libretto.{CoreBridge, CoreDSL, Monad}
import libretto.util.{Async, Monad => ScalaMonad}
import libretto.util.Monad.syntax._

trait TestKit {
  val dsl: CoreDSL

  opaque type F[A] = Async[A]

  opaque type Outcome[A] = F[TestResult[A]]
  object Outcome {
    def apply[A](fa: F[TestResult[A]]): Outcome[A] =
      fa

    def asyncTestResult[A](fa: Async[TestResult[A]]): Outcome[A] =
      fa

    def unwrap[A](outcome: Outcome[A]): F[TestResult[A]] =
      outcome

    def toAsyncTestResult[A](outcome: Outcome[A]): Async[TestResult[A]] =
      outcome

    def fromTestResult[A](res: TestResult[A]): Outcome[A] =
      Outcome(Async.now(res))

    def success[A](a: A): Outcome[A] =
      fromTestResult(TestResult.success(a))

    def failure[A](msg: String): Outcome[A] =
      fromTestResult(TestResult.failure(msg))

    def crash[A](e: Throwable): Outcome[A] =
      fromTestResult(TestResult.crash(e))

    def successF[A](fa: F[A]): Outcome[A] =
      Outcome(fa.map(TestResult.success))

    def assert(condition: Boolean, failMsg: String = "Assertion failed"): Outcome[Unit] =
      if (condition)
        success(())
      else
        failure(failMsg)

    def assertEquals[A](actual: A, expected: A): Outcome[Unit] =
      assert(
        actual == expected,
        failMsg = s"$actual did not equal $expected",
      )

    def traverseIterator[A, B](it: Iterator[A])(f: A => Outcome[B]): Outcome[List[B]] =
      if (it.hasNext) {
        monadOutcome.flatMap(f(it.next()))(b => monadOutcome.map(traverseIterator(it)(f))(b :: _))
      } else {
        success(Nil)
      }

    def traverse[A, B](as: Iterable[A])(f: A => Outcome[B]): Outcome[List[B]] =
      traverseIterator(as.iterator)(f)

    def traverseList[A, B](as: List[A])(f: A => Outcome[B]): Outcome[List[B]] =
      as match {
        case Nil => success(Nil)
        case h :: t => monadOutcome.flatMap(f(h))(b => monadOutcome.map(traverseList(t)(f))(b :: _))
      }
  }

  val probes: CoreBridge.Of[dsl.type]

  import dsl.{-⚬, |*|, |+|, Done}
  import probes.Execution

  type Assertion[A]

  def success[A]: A -⚬ Assertion[A]
  def failure[A]: Done -⚬ Assertion[A]

  given monadAssertion: Monad[-⚬, Assertion]

  def extractOutcome(using exn: Execution)(outPort: exn.OutPort[Assertion[Done]]): Outcome[Unit]

  given monadOutcome: ScalaMonad[Outcome] with {
    override def pure[A](a: A): Outcome[A] =
      Async.now(TestResult.success(a))

    override def flatMap[A, B](fa: Outcome[A])(f: A => Outcome[B]): Outcome[B] =
      fa.flatMap {
        case TestResult.Success(a)   => f(a)
        case TestResult.Failure(msg) => Async.now(TestResult.Failure(msg))
        case TestResult.Crash(e)     => Async.now(TestResult.Crash(e))
      }
  }

  def splitOut[A, B](using exn: Execution)(port: exn.OutPort[A |*| B]): Outcome[(exn.OutPort[A], exn.OutPort[B])] =
    Outcome.success(exn.OutPort.split(port))

  def expectDone(using exn: Execution)(port: exn.OutPort[Done]): Outcome[Unit] =
    exn.OutPort.awaitDone(port).map {
      case Left(e)   => TestResult.crash(e)
      case Right(()) => TestResult.success(())
    }

  def expectCrashDone(using exn: Execution)(port: exn.OutPort[Done]): Outcome[Throwable] =
    exn.OutPort.awaitDone(port).map {
      case Left(e)   => TestResult.success(e)
      case Right(()) => TestResult.failure("Expected crash, but got Done")
    }

  def expectLeft[A, B](using exn: Execution)(port: exn.OutPort[A |+| B]): Outcome[exn.OutPort[A]] =
    exn.OutPort.awaitEither(port).map {
      case Left(e)         => TestResult.crash(e)
      case Right(Left(p))  => TestResult.success(p)
      case Right(Right(_)) => TestResult.failure("Expected Left, but got Right")
    }

  def expectRight[A, B](using exn: Execution)(port: exn.OutPort[A |+| B]): Outcome[exn.OutPort[B]] =
    exn.OutPort.awaitEither(port).map {
      case Left(e)         => TestResult.crash(e)
      case Right(Left(_))  => TestResult.failure("Expected Right, but got Left")
      case Right(Right(p)) => TestResult.success(p)
    }
}

object TestKit {
  transparent inline def givenInstance(using kit: TestKit): kit.type =
    kit

  transparent inline def dsl(using kit: TestKit): kit.dsl.type =
    kit.dsl

  def success(using kit: TestKit): kit.dsl.-⚬[kit.dsl.Done, kit.Assertion[dsl.Done]] =
    kit.success
}
