package libretto.lambda.examples.workflow.generic.vis

import libretto.lambda.examples.workflow.generic.lang
import libretto.lambda.examples.workflow.generic.lang.{++, *}

sealed trait OpTag[Op <: AnyKind]

object OpTag {
  case object Pair extends OpTag[**]
  case object Sum extends OpTag[++]
  case object Enum extends OpTag[lang.Enum]

  def apply[Op <: AnyKind](using op: OpTag[Op]): OpTag[Op] =
    op

  given OpTag[++] = Sum
  given OpTag[**] = Pair
  given OpTag[lang.Enum] = Enum
}
