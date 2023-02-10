package libretto

import libretto.scaletto.StarterKit

package object stream {
  val DefaultStreams =
    CoreStreams(
      StarterKit.dsl,
      StarterKit.coreLib,
    )
}
