package libretto.testing

import java.util.concurrent.{Executors, ExecutorService, ScheduledExecutorService}
import libretto.{ScalaRunner, StarterKit}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.BeforeAndAfterAll
import scala.concurrent.{Await, Future}
import scala.concurrent.duration._
import scala.util.{Failure, Success}

abstract class TestSuite extends AnyFunSuite with BeforeAndAfterAll {
  val kit = StarterKit
  import kit.dsl._
  import kit.coreLib._
  import kit.coreStreams._

  private var scheduler: ScheduledExecutorService = _
  private var blockingExecutor: ExecutorService = _
  private var runner: ScalaRunner[kit.dsl.type, Future] = _

  override def beforeAll(): Unit = {
    scheduler = Executors.newScheduledThreadPool(2)
    blockingExecutor = Executors.newCachedThreadPool()
    runner = StarterKit.runner(blockingExecutor)(scheduler)
  }

  override def afterAll(): Unit = {
    blockingExecutor.shutdown()
    scheduler.shutdown()
  }

  def assertCompletes(prg: Done -⚬ Done): Unit =
    Await.result(
      runner.run(prg),
      5.seconds,
    )

  def assertCocompletes(prg: Need -⚬ Need): Unit =
    assertCompletes(introSnd(lInvertSignal > fst(prg)) > assocRL > elimFst(rInvertSignal))

  def assertVal[A](prg: Done -⚬ Val[A], expected: A): Unit =
    assert(Await.result(runner.runScala(prg), 5.seconds) == expected)

  def testVal[A](prg: Done -⚬ Val[A])(f: A => Unit): Unit =
    f(Await.result(runner.runScala(prg), 5.seconds))

  def assertCrashes(prg: Done -⚬ Done, expectedMsg: Option[String] = None): Unit =
    Await.ready(runner.run(prg), 5.seconds).value.get match {
      case Success(()) =>
        assert(false, "Expected crash, but the program completed successfully.")
      case Failure(e) =>
        expectedMsg.foreach { msg =>
          assert(e.getMessage == msg, s"Expected message $msg, actual exception: $e")
        }
    }

  def assertCrashes(prg: Done -⚬ Done, expectedMsg: String): Unit =
    assertCrashes(prg, Some(expectedMsg))

  def assertLeft[A, B]: (A |+| B) -⚬ A =
    either(id, crashNow("Expected left, was right"))

  def assertRight[A, B]: (A |+| B) -⚬ B =
    either(crashNow("Expected right, was left"), id)

  extension [A, B: Junction.Positive](f: A -⚬ LPollable[B]) {
    def expectPoll: A -⚬ LPollable[B] =
      f > LPollable.from(
        onClose = LPollable.close > crashd("Expected poll, received close"),
        onPoll = LPollable.poll,
      )

    def timeout(d: FiniteDuration): A -⚬ LPollable[B] = {
      import LPollable._

      val msg = s"No action (poll or close) within $d"

      f.from[A]                     .to[          LPollable[B]         ]
        .choice(crashNow(msg), id)  .to[ LPollable[B] |&| LPollable[B] ]
        .>(selectAgainstL)          .to[         Need |*| LPollable[B] ]
        .>.fst(delayNeed(d))        .to[         Need |*| LPollable[B] ]
        .elimFst(need)              .to[                  LPollable[B] ]
    }
  }
}
