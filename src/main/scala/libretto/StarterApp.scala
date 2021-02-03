package libretto

import java.util.concurrent.Executors
import scala.concurrent.ExecutionContext
import scala.util.{Failure, Success}

abstract class StarterApp extends StarterKit {
  import dsl._

  def blueprint: One -⚬ Done

  def main(args: Array[String]): Unit = {
    val mainExecutor = Executors.newScheduledThreadPool(8)
    val blockingExecutor = Executors.newCachedThreadPool()
    implicit val ec = ExecutionContext.fromExecutor(mainExecutor)

    runner(blockingExecutor)(mainExecutor)
      .run(blueprint)
      .onComplete { res =>
        res match {
          case Success(_) => // do nothing
          case Failure(e) => e.printStackTrace
        }
        blockingExecutor.shutdown()
        mainExecutor.shutdown()
      }
  }
}
