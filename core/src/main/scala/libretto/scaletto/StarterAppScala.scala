package libretto.scaletto

import java.util.concurrent.Executors
import libretto.scaletto.StarterKit.runScalaAsync
import scala.concurrent.duration.Duration
import scala.concurrent.{Await, ExecutionContext}
import scala.util.{Failure, Success}

abstract class StarterAppScala[A] extends StarterAppBase {
  def blueprint: Done -⚬ Val[A]

  def main(args: Array[String]): Unit = {
    val a = Await.result(runScalaAsync(blueprint), Duration.Inf)
    println(a)
  }
}
