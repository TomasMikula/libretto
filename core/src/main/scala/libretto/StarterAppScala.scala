package libretto

import java.util.concurrent.Executors
import scala.concurrent.{Await, ExecutionContext}
import scala.concurrent.duration.Duration
import scala.util.{Failure, Success}

abstract class StarterAppScala[A] extends StarterKit {
  import dsl._

  def blueprint: One -⚬ Val[A]

  def main(args: Array[String]): Unit = {
    val a = Await.result(runScalaAsync(blueprint), Duration.Inf)
    println(a)
  }
}
