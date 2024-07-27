package libretto.testing.scaletto

import libretto.scaletto.StarterKit
import libretto.testing.TestKit

type StarterTestKit = ScalettoTestKit & TestKit.OfDsl[StarterKit.dsl.type]
