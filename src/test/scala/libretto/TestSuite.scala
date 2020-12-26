package libretto

import org.scalatest.funsuite.AnyFunSuite
import scala.concurrent.{Await, ExecutionContext}
import scala.concurrent.duration._

abstract class TestSuite extends AnyFunSuite {
  val kit = StarterKit
  import kit.dsl._
  import kit.coreLib._
  
  val runner = StarterKit.runner(ExecutionContext.global)

  def assertCompletes(prg: One -⚬ Done): Unit =
    Await.result(
      runner.run(prg),
      5.seconds,
    )

  def assertResult[A](prg: One -⚬ Val[A], expected: A): Unit =
    assert(Await.result(runner.runScala(prg), 5.seconds) == expected)
}
