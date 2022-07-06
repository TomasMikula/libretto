package libretto

import java.util.concurrent.ScheduledExecutorService

package object mashup {
  val kit: MashupKit = MashupKitImpl

  val dsl: kit.dsl.type = kit.dsl

  def createRuntime(executor: ScheduledExecutorService): MashupRuntime[dsl.type] =
    kit.createRuntime(executor)
}
