package libretto.stream

import libretto.scaletto.StarterKit

val DefaultStreams =
  InvertStreams(
    StarterKit.dsl,
    StarterKit.coreLib,
  )
