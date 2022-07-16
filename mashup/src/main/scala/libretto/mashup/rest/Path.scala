package libretto.mashup.rest

import Path._

enum Path {
  case Empty
  case NonEmpty(initialSegments: List[Segment], lastSegment: LastSegment)
}

object Path {
  opaque type Segment = String

  def segment(s: String): Segment =
    s

  extension (seg: Segment) {
    def asString: String = seg
  }

  sealed trait LastSegment {
    def segment: Segment
  }
  object LastSegment {
    case class NonEmpty(value: Segment) extends LastSegment {
      require(value.nonEmpty)

      override def segment: Segment =
        value
    }

    case class SlashTerminated(value: Segment) extends LastSegment {
      override def segment: Segment =
        value
    }
  }
}
