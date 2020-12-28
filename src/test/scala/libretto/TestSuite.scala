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

  def assertResult[A](prg: One -⚬ Val[A], expected: A): Unit =
    assert(Await.result(runner.runScala(prg), 5.seconds) == expected)
    
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
}
