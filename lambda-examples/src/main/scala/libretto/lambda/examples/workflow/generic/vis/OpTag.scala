package libretto.lambda.examples.workflow.generic.vis

import libretto.lambda.examples.workflow.generic.lang.{++, **}

enum OpTag[Op <: AnyKind] {
  case Pair extends OpTag[**]
  case Sum extends OpTag[++]
}

object OpTag {
  given OpTag[++] = Sum
  given OpTag[**] = Pair
}
