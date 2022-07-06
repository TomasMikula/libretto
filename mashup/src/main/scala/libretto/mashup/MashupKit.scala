package libretto.mashup

import java.util.concurrent.ScheduledExecutorService

trait MashupKit {
  val dsl: MashupDsl

  def createRuntime(executor: ScheduledExecutorService): MashupRuntime[dsl.type]
}
