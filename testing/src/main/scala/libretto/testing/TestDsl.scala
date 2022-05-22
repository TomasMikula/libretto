package libretto.testing

import libretto.{CoreBridge, CoreDSL}
import libretto.{testing => lt}
import libretto.util.Monad
import libretto.util.Monad.syntax._

trait TestDsl {
  val dsl: CoreDSL

  type F[_]

  given F: Monad[F]

  opaque type Outcome[A] = F[lt.TestResult[A]]
  object Outcome {
    def apply[A](fa: F[lt.TestResult[A]]): Outcome[A] =
      fa

    def unwrap[A](outcome: Outcome[A]): F[lt.TestResult[A]] =
      outcome

    def fromTestResult[A](res: lt.TestResult[A]): Outcome[A] =
      Outcome(F.pure(res))

    def success[A](a: A): Outcome[A] =
      fromTestResult(lt.TestResult.success(a))

    def failure[A](msg: String): Outcome[A] =
      fromTestResult(lt.TestResult.failure(msg))

    def crash[A](e: Throwable): Outcome[A] =
      fromTestResult(lt.TestResult.crash(e))

    def successF[A](fa: F[A]): Outcome[A] =
      Outcome(fa.map(lt.TestResult.success))

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

  type TestResult

  import dsl.{-⚬, |*|, |+|, Done}
  import probes.OutPort

  type TestCase = Done -⚬ TestResult

  def success: Done -⚬ TestResult
  def failure: Done -⚬ TestResult

  def extractTestResult(outPort: OutPort[TestResult]): Outcome[Unit]

  given monadOutcome: Monad[Outcome] with {
    override def pure[A](a: A): Outcome[A] =
      F.pure(TestResult.success(a))

    override def flatMap[A, B](fa: Outcome[A])(f: A => Outcome[B]): Outcome[B] =
      F.flatMap(fa) {
        case lt.TestResult.Success(a)   => f(a)
        case lt.TestResult.Failure(msg) => F.pure(lt.TestResult.Failure(msg))
        case lt.TestResult.Crash(e)     => F.pure(lt.TestResult.Crash(e))
      }
  }

  def splitOut[A, B](port: OutPort[A |*| B]): Outcome[(OutPort[A], OutPort[B])] =
    Outcome.successF(probes.splitOut(port))

  def expectDone(port: OutPort[Done]): Outcome[Unit] =
    probes.awaitDone(port).map {
      case Left(e)   => lt.TestResult.crash(e)
      case Right(()) => lt.TestResult.success(())
    }

  def expectCrashDone(port: OutPort[Done]): Outcome[Throwable] =
    probes.awaitDone(port).map {
      case Left(e)   => lt.TestResult.success(e)
      case Right(()) => lt.TestResult.failure("Expected crash, but got Done")
    }

  def expectLeft[A, B](port: OutPort[A |+| B]): Outcome[OutPort[A]] =
    probes.awaitEither(port).map {
      case Left(e)         => lt.TestResult.crash(e)
      case Right(Left(p))  => lt.TestResult.success(p)
      case Right(Right(_)) => lt.TestResult.failure("Expected Left, but got Right")
    }

  def expectRight[A, B](port: OutPort[A |+| B]): Outcome[OutPort[B]] =
    probes.awaitEither(port).map {
      case Left(e)         => lt.TestResult.crash(e)
      case Right(Left(_))  => lt.TestResult.failure("Expected Right, but got Left")
      case Right(Right(p)) => lt.TestResult.success(p)
    }
}

object TestDsl {
  transparent inline def givenInstance(using testDsl: TestDsl): testDsl.type =
    testDsl

  transparent inline def dsl(using testDsl: TestDsl): testDsl.dsl.type =
    testDsl.dsl

  def success(using testDsl: TestDsl): testDsl.dsl.-⚬[testDsl.dsl.Done, testDsl.TestResult] =
    testDsl.success
}
