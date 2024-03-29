package libretto.scaletto

import libretto.scaletto.StarterKit.runAsync
import scala.concurrent.Await
import scala.concurrent.duration.Duration

abstract class StarterApp extends StarterAppBase {
  def blueprint: Done -⚬ Done

  def main(args: Array[String]): Unit = {
    Await.result(runAsync(blueprint), Duration.Inf)
  }
}
