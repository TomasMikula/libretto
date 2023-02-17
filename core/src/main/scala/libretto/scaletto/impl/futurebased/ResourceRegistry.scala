package libretto.scaletto.impl.futurebased

import libretto.util.Async
import scala.collection.mutable

private class ResourceRegistry {
  import ResourceRegistry._

  // negative value indicates registry closed
  private var lastResId: Long =
    0L

  private val resourceMap: mutable.Map[Long, AcquiredResource[?]] =
    mutable.Map()

  def registerResource[R](resource: R, releaseAsync: R => Async[Unit]): RegisterResult =
    synchronized {
      if (lastResId < 0L) {
        assert(resourceMap.isEmpty)
        RegisterResult.RegistryClosed
      } else {
        lastResId += 1
        val id = lastResId
        resourceMap.put(id, AcquiredResource(resource, releaseAsync))
        RegisterResult.Registered(resId(id))
      }
    }

  def unregisterResource(id: ResId): UnregisterResult =
    synchronized {
      if (lastResId < 0l) {
        assert(resourceMap.isEmpty)
        UnregisterResult.RegistryClosed
      } else {
        resourceMap.remove(id.value) match {
          case None => UnregisterResult.NotFound
          case Some(r) => UnregisterResult.Unregistered(r)
        }
      }
    }

  def close(): Seq[AcquiredResource[?]] =
    synchronized {
      if (lastResId < 0L) {
        assert(resourceMap.isEmpty)
        Seq.empty
      } else {
        lastResId = Long.MinValue
        val result = resourceMap.values.toSeq
        resourceMap.clear()
        result
      }
    }
}

private object ResourceRegistry {
  opaque type ResId = Long
  private def resId(value: Long): ResId = value
  extension (resId: ResId) {
    def value: Long = resId
  }

  sealed trait RegisterResult
  object RegisterResult {
    case class Registered(id: ResId) extends RegisterResult
    case object RegistryClosed extends RegisterResult
  }

  sealed trait UnregisterResult
  object UnregisterResult {
    case class Unregistered(value: AcquiredResource[?]) extends UnregisterResult
    case object NotFound extends UnregisterResult
    case object RegistryClosed extends UnregisterResult
  }

  case class AcquiredResource[A](resource: A, releaseAsync: A => Async[Unit])
}
