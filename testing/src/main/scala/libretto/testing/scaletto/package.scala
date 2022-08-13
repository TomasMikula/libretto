package libretto.testing

import libretto.scaletto.StarterKit

package object scaletto {
  type StarterTestKit = ScalettoTestKit.Of[StarterKit.dsl.type]
}
