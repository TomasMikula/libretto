package libretto.stream

import libretto.scaletto.StarterKit

package object scaletto {
  val Default =
    ScalettoStreams(
      StarterKit.dsl,
      StarterKit.coreLib,
      StarterKit.scalettoLib,
      StarterKit.coreStreams,
    )
}
