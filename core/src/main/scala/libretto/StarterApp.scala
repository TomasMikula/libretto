package libretto

import libretto.StarterKit.runAsync
import scala.concurrent.Await
import scala.concurrent.duration.Duration

abstract class StarterApp extends StarterAppBase {
  def blueprint: One -⚬ Done

  def main(args: Array[String]): Unit = {
    Await.result(runAsync(blueprint), Duration.Inf)
  }
}
