package libretto

import java.util.concurrent.Executors
import scala.concurrent.{Await, ExecutionContext}
import scala.concurrent.duration.Duration
import scala.util.{Failure, Success}

abstract class StarterApp extends StarterKit {
  import dsl._

  def blueprint: One -⚬ Done

  def main(args: Array[String]): Unit = {
    Await.result(runAsync(blueprint), Duration.Inf)
  }
}
