package libretto

import java.util.concurrent.{Executors, ScheduledExecutorService}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.BeforeAndAfterAll
import scala.concurrent.{Await, Future}
import scala.concurrent.duration._
import scala.util.{Failure, Success}

abstract class TestSuite extends AnyFunSuite with BeforeAndAfterAll {
  val kit = StarterKit
  import kit.dsl._
  import kit.coreLib._
  import kit.crashLib._
  import kit.coreStreams._
  
  private var scheduler: ScheduledExecutorService = _
  private var runner: ScalaRunner[kit.dsl.type, Future] = _
  
  override def beforeAll(): Unit = {
    scheduler = Executors.newScheduledThreadPool(2)
    runner = StarterKit.runner(scheduler)
  }
  
  override def afterAll(): Unit = {
    scheduler.shutdown()
  }

  def assertCompletes(prg: One -⚬ Done): Unit =
    Await.result(
      runner.run(prg),
      5.seconds,
    )

  def assertVal[A](prg: One -⚬ Val[A], expected: A): Unit =
    assert(Await.result(runner.runScala(prg), 5.seconds) == expected)
    
  def testVal[A](prg: One -⚬ Val[A])(f: A => Unit): Unit =
    f(Await.result(runner.runScala(prg), 5.seconds))

  def assertCrashes(prg: One -⚬ Done, expectedMsg: Option[String] = None): Unit =
    Await.ready(runner.run(prg), 5.seconds).value.get match {
      case Success(()) =>
        assert(false, "Expected crash, but the program completed successfully.")
      case Failure(e) =>
        expectedMsg.foreach { msg =>
          assert(e.getMessage == msg, s"Expected message $msg, actual exception: $e")
        }
    }

  def assertCrashes(prg: One -⚬ Done, expectedMsg: String): Unit = 
    assertCrashes(prg, Some(expectedMsg))

  extension [A, B: Junction.Positive](f: A -⚬ LPollable[B]) {
    def expectPoll: A -⚬ LPollable[B] =
      f >>> LPollable.from(
        onClose = LPollable.close >>> crashd("Expected poll, received close"),
        onPoll = LPollable.poll,
      )

    def timeout(d: FiniteDuration): A -⚬ LPollable[B] = {
      import LPollable._

      val msg = s"No action (poll or close) within $d"
      
      f.from[A]                     .to[          LPollable[B]         ]
        .choice(crashPos(msg), id)  .to[ LPollable[B] |&| LPollable[B] ]
        .>(selectAgainstL)          .to[         Need |*| LPollable[B] ]
        .>.fst(delayNeed(d))        .to[         Need |*| LPollable[B] ]
        .elimFst(need)              .to[                  LPollable[B] ]
    }
  }
}
