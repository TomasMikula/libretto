package libretto.stream

import libretto.scaletto.StarterKit

package object scaletto {
  val DefaultStreams =
    ScalettoStreams(
      StarterKit.dsl,
      StarterKit.coreLib,
      StarterKit.scalettoLib,
      libretto.stream.DefaultStreams,
    )
}
