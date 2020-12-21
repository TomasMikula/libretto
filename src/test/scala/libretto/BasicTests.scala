package libretto

import scala.concurrent.{Await, ExecutionContext}
import scala.concurrent.duration._

class BasicTests extends TestSuite {
  import kit.dsl._
  import kit.coreLib._
  
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
