package libretto.testing

import libretto.StarterKit

trait StarterTestKit extends ScalaTestKit {
  override val dsl: StarterKit.dsl.type
}
