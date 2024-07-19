package libretto.stream.scaletto

import libretto.scaletto.StarterKit

val DefaultStreams =
  ScalettoStreams(
    StarterKit.dsl,
    StarterKit.coreLib,
    StarterKit.scalettoLib,
    libretto.stream.invert.DefaultStreams,
  )
