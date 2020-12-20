package libretto

import org.scalatest.funsuite.AnyFunSuite
import scala.concurrent.{Await, ExecutionContext}
import scala.concurrent.duration._

class BasicTests extends AnyFunSuite {
  import StarterKit.dsl._
  import StarterKit.coreLib._
  
  val runner = StarterKit.runner(ExecutionContext.global)
  
  private def testCompletion(name: String)(prg: One -⚬ Done): Unit = {
    test(name) {
      Await.result(
        runner.run(prg),
        5.seconds,
      )
    }
  }
  
  private def testResult[A](name: String)(prg: One -⚬ Val[A])(expected: A): Unit = {
    test(name) {
      assert(Await.result(runner.runScala(prg), 5.seconds) == expected)
    }
  }
  
  testCompletion("done") {
    done
  }
  
  testCompletion("join ⚬ fork") {
    done >>> fork >>> join
  }
  
  testResult("constVal") {
    done >>> constVal(5)
  } (
    5
  )
}
