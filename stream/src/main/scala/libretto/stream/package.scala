package libretto

import libretto.scaletto.StarterKit

package object stream {
  val DefaultStreams =
    InvertStreams(
      StarterKit.dsl,
      StarterKit.coreLib,
    )
}
