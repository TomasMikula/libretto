package libretto

import java.util.concurrent.Executors
import libretto.StarterKit.dsl._
import libretto.StarterKit.runAsync
import scala.concurrent.duration.Duration
import scala.concurrent.{Await, ExecutionContext}
import scala.util.{Failure, Success}

abstract class StarterAppBase {
  export StarterKit.dsl._
  export StarterKit.coreLib.{dsl => _, _}
  export StarterKit.scalaLib.{dsl => _, _}
  export StarterKit.coreStreams.{dsl => _, _}
  export StarterKit.scalaStreams.{dsl => _, coreLib => _, _}
}
