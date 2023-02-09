package libretto.testing

import libretto.{CoreBridge, CoreDSL, ExecutionParams, Monad}
import libretto.lambda.util.{Monad => ScalaMonad, SourcePos}
import libretto.lambda.util.Monad.syntax._
import libretto.util.Async

trait TestKit {
  type Dsl <: CoreDSL

  val dsl: Dsl

  opaque type Outcome[A] = Async[TestResult[A]]
  object Outcome {
    def asyncTestResult[A](fa: Async[TestResult[A]]): Outcome[A] =
      fa

    def toAsyncTestResult[A](outcome: Outcome[A]): Async[TestResult[A]] =
      outcome

    def fromTestResult[A](res: TestResult[A]): Outcome[A] =
      Async.now(res)

    def success[A](a: A): Outcome[A] =
      fromTestResult(TestResult.success(a))

    def expectThrows[A](using pos: SourcePos)(a: => A): Outcome[Throwable] =
      try {
        a
        failure(using pos)("Expected exception, nothing was thrown")
      } catch {
        case e => success(e)
      }

    def expectThrows[A, B](using pos: SourcePos)(a: => A)(recover: PartialFunction[Throwable, B]): Outcome[B] =
      monadOutcome.flatMap(expectThrows(using pos)(a)) {
        case recover(b) => success(b)
        case e          => crash(e)
      }

    def expectNotThrows[A](using pos: SourcePos)(a: => A): Outcome[Unit] =
      try {
        a
        success(())
      } catch {
        case e => failure(using pos)(s"Failed with exception: $e", Some(e))
      }

    def failure[A](using pos: SourcePos)(
      msg: String,
      error: Option[Throwable] = None,
    ): Outcome[A] =
      fromTestResult(TestResult.failure(using pos)(msg, error))

    def crash[A](e: Throwable): Outcome[A] =
      fromTestResult(TestResult.crash(e))

    def assert(using pos: SourcePos)(condition: Boolean, failMsg: String = "Assertion failed"): Outcome[Unit] =
      if (condition)
        success(())
      else
        failure(using pos)(failMsg)

    /** Alias for [[assert]]. */
    def assertTrue(using pos: SourcePos)(condition: Boolean): Outcome[Unit] =
      assert(using pos)(condition)

    /** Alias for [[assert]]. */
    def assertTrue(using pos: SourcePos)(condition: Boolean, failMsg: String): Outcome[Unit] =
      assert(using pos)(condition, failMsg)

    def assertEquals[A](actual: A, expected: A)(using pos: SourcePos): Outcome[Unit] =
      assert(using pos)(
        actual == expected,
        failMsg = s"$actual did not equal $expected",
      )

    def assertSubstring(using pos: SourcePos)(substr: String, str: String): Outcome[Unit] =
      assert(using pos)(
        str contains substr,
        s"'$str' did not contain '$substr'",
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

    extension [A](outcome: Outcome[A]) {
      def assertEquals(using pos: SourcePos)(expected: A): Outcome[Unit] =
        monadOutcome.flatMap(outcome)(a => Outcome.assertEquals(a, expected)(using pos))
    }
  }

  val bridge: CoreBridge.Of[dsl.type]

  import dsl.{-⚬, |*|, |+|, Done, Ping}
  import bridge.Execution

  type Assertion[A]

  def success[A]: A -⚬ Assertion[A]
  def failure[A]: Done -⚬ Assertion[A]

  given monadAssertion: Monad[-⚬, Assertion]

  def extractOutcome(using exn: Execution, pos: SourcePos)(
    outPort: exn.OutPort[Assertion[Done]],
  ): Outcome[Unit]

  type ExecutionParam[A]
  val ExecutionParam: ExecutionParams[ExecutionParam]

  given monadOutcome: ScalaMonad[Outcome] with {
    override def pure[A](a: A): Outcome[A] =
      Async.now(TestResult.success(a))

    override def flatMap[A, B](fa: Outcome[A])(f: A => Outcome[B]): Outcome[B] =
      fa.flatMap {
        case TestResult.Success(a)           => f(a)
        case TestResult.Failure(msg, pos, e) => Async.now(TestResult.Failure(msg, pos, e))
        case TestResult.Crash(e)             => Async.now(TestResult.Crash(e))
        case TestResult.TimedOut(d)          => Async.now(TestResult.TimedOut(d))
      }
  }

  def splitOut[A, B](using exn: Execution)(port: exn.OutPort[A |*| B]): Outcome[(exn.OutPort[A], exn.OutPort[B])] =
    Outcome.success(exn.OutPort.split(port))

  def expectDone(using exn: Execution)(port: exn.OutPort[Done]): Outcome[Unit] =
    exn.OutPort.awaitDone(port).map {
      case Left(e)   => TestResult.crash(e)
      case Right(()) => TestResult.success(())
    }

  def expectCrashDone(using exn: Execution, pos: SourcePos)(port: exn.OutPort[Done]): Outcome[Throwable] =
    exn.OutPort.awaitDone(port).map {
      case Left(e)   => TestResult.success(e)
      case Right(()) => TestResult.failure(using pos)("Expected crash, but got Done")
    }

  def expectPing(using exn: Execution)(port: exn.OutPort[Ping]): Outcome[Unit] =
    exn.OutPort.awaitPing(port).map {
      case Left(e)   => TestResult.crash(e)
      case Right(()) => TestResult.success(())
    }

  def expectLeft[A, B](using exn: Execution, pos: SourcePos)(port: exn.OutPort[A |+| B]): Outcome[exn.OutPort[A]] =
    exn.OutPort.awaitEither(port).map {
      case Left(e)         => TestResult.crash(e)
      case Right(Left(p))  => TestResult.success(p)
      case Right(Right(_)) => TestResult.failure(using pos)("Expected Left, but got Right")
    }

  def expectRight[A, B](using exn: Execution, pos: SourcePos)(port: exn.OutPort[A |+| B]): Outcome[exn.OutPort[B]] =
    exn.OutPort.awaitEither(port).map {
      case Left(e)         => TestResult.crash(e)
      case Right(Left(_))  => TestResult.failure(using pos)("Expected Right, but got Left")
      case Right(Right(p)) => TestResult.success(p)
    }
}

object TestKit extends TestKitOps

trait TestKitOps {
  transparent inline def givenInstance(using kit: TestKit): kit.type =
    kit

  transparent inline def dsl(using kit: TestKit): kit.dsl.type =
    kit.dsl

  transparent inline def bridge(using kit: TestKit): kit.bridge.type =
    kit.bridge

  def success(using kit: TestKit): kit.dsl.-⚬[kit.dsl.Done, kit.Assertion[dsl.Done]] =
    kit.success
}
