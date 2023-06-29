package libretto.mashup

import java.util.concurrent.ScheduledExecutorService
import libretto.util.Async
import zio.ZIO

val kit: MashupKit = MashupKitImpl

val dsl: kit.dsl.type = kit.dsl

type Runtime = MashupRuntime[dsl.type]

object Runtime {
  def create(executor: ScheduledExecutorService): Runtime =
    kit.createRuntime(executor)
}

extension [A](a: Async[A]) {
  def toZIO: ZIO[Any, Nothing, A] =
    a match {
      case Async.Now(a) =>
        ZIO.succeed(a)
      case Async.Later(register) =>
        ZIO.async(callback => register(a => callback(ZIO.succeed(a))))
    }
}
