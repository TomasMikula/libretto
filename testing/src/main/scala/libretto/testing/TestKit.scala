package libretto.testing

import libretto.{CoreBridge, CoreDSL, Monad}
import libretto.util.{Monad => ScalaMonad}
import libretto.util.Monad.syntax._

trait TestKit {
  val dsl: CoreDSL

  type F[_]

  given F: ScalaMonad[F]

  opaque type Outcome[A] = F[TestResult[A]]
  object Outcome {
    def apply[A](fa: F[TestResult[A]]): Outcome[A] =
      fa

    def unwrap[A](outcome: Outcome[A]): F[TestResult[A]] =
      outcome

    def fromTestResult[A](res: TestResult[A]): Outcome[A] =
      Outcome(F.pure(res))

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
        f(it.next()).flatMap(b => traverseIterator(it)(f).map(b :: _))
      } else {
        success(Nil)
      }

    def traverse[A, B](as: Iterable[A])(f: A => Outcome[B]): Outcome[List[B]] =
      traverseIterator(as.iterator)(f)

    def traverseList[A, B](as: List[A])(f: A => Outcome[B]): Outcome[List[B]] =
      as match {
        case Nil => success(Nil)
        case h :: t => f(h).flatMap(b => traverseList(t)(f).map(b :: _))
      }
  }

  val probes: CoreBridge.Of[dsl.type, F]

  import dsl.{-⚬, |*|, |+|, Done}
  import probes.OutPort

  type Assertion[A]

  def success[A]: A -⚬ Assertion[A]
  def failure[A]: Done -⚬ Assertion[A]

  given monadAssertion: Monad[-⚬, Assertion]

  def extractOutcome(outPort: OutPort[Assertion[Done]]): Outcome[Unit]

  given monadOutcome: ScalaMonad[Outcome] with {
    override def pure[A](a: A): Outcome[A] =
      F.pure(TestResult.success(a))

    override def flatMap[A, B](fa: Outcome[A])(f: A => Outcome[B]): Outcome[B] =
      F.flatMap(fa) {
        case TestResult.Success(a)   => f(a)
        case TestResult.Failure(msg) => F.pure(TestResult.Failure(msg))
        case TestResult.Crash(e)     => F.pure(TestResult.Crash(e))
      }
  }

  def splitOut[A, B](port: OutPort[A |*| B]): Outcome[(OutPort[A], OutPort[B])] =
    Outcome.successF(probes.splitOut(port))

  def expectDone(port: OutPort[Done]): Outcome[Unit] =
    probes.awaitDone(port).map {
      case Left(e)   => TestResult.crash(e)
      case Right(()) => TestResult.success(())
    }

  def expectCrashDone(port: OutPort[Done]): Outcome[Throwable] =
    probes.awaitDone(port).map {
      case Left(e)   => TestResult.success(e)
      case Right(()) => TestResult.failure("Expected crash, but got Done")
    }

  def expectLeft[A, B](port: OutPort[A |+| B]): Outcome[OutPort[A]] =
    probes.awaitEither(port).map {
      case Left(e)         => TestResult.crash(e)
      case Right(Left(p))  => TestResult.success(p)
      case Right(Right(_)) => TestResult.failure("Expected Left, but got Right")
    }

  def expectRight[A, B](port: OutPort[A |+| B]): Outcome[OutPort[B]] =
    probes.awaitEither(port).map {
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
