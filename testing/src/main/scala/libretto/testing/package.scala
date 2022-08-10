package libretto

import libretto.StarterKit

package object testing {
  type StarterTestKit = ScalaTestKit.Of[StarterKit.dsl.type]
}
