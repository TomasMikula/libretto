package libretto

import org.scalatest.funsuite.AnyFunSuite
import scala.concurrent.{Await, ExecutionContext}
import scala.concurrent.duration._

abstract class TestSuite extends AnyFunSuite {
  val kit = StarterKit
  import kit.dsl._
  import kit.coreLib._
  
  val runner = StarterKit.runner(ExecutionContext.global)

  def testCompletion(name: String)(prg: One -⚬ Done): Unit = {
    test(name) {
      Await.result(
        runner.run(prg),
        5.seconds,
      )
    }
  }

  def testResult[A](name: String)(prg: One -⚬ Val[A])(expected: A): Unit = {
    test(name) {
      assert(Await.result(runner.runScala(prg), 5.seconds) == expected)
    }
  }
}
