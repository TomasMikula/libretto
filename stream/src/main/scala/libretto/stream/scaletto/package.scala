package libretto.stream.scaletto

import libretto.scaletto.StarterKit

val DefaultStreams =
  ScalettoStreams(
    StarterKit.dsl,
    StarterKit.puroLib,
    StarterKit.scalettoLib,
    libretto.stream.invert.DefaultStreams,
  )
