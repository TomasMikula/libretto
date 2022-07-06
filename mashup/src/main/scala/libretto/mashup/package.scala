package libretto

import java.util.concurrent.ScheduledExecutorService

package object mashup {
  val kit: MashupKit = MashupKitImpl

  val dsl: kit.dsl.type = kit.dsl

  type Runtime = MashupRuntime[dsl.type]

  object Runtime {
    def create(executor: ScheduledExecutorService): Runtime =
      kit.createRuntime(executor)
  }
}
