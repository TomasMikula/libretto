package libretto.lambda.examples.workflow.generic.vis

sealed trait Connector[X, Y]

object Connector {
  case class Across[X, Y](
    src: WirePick[X],
    tgt: WirePick[Y],
    style: Across.Style = Across.Style.default,
  ) extends Connector[X, Y] {
    def styled(style: Across.Style): Connector[X, Y] =
      copy(style = style)

    def fill(fill: Color | PredefinedFill): Connector[X, Y] =
      styled(this.style.copy(fill = fill))

    def floodArea(fill: Color | PredefinedFill): Connector[X, Y] =
      styled(this.style.copy(areaFill = Some(fill)))
  }

  object Across {
    case class Style(
      fill: Color | PredefinedFill,
      areaFill: Option[Color | PredefinedFill],
    )

    object Style {
      def default: Style = Style(Color.Black, areaFill = None)
    }
  }

  case class LoopIn[X, Y](
    src: WirePick[X],
    tgt: WirePick[X],
  ) extends Connector[X, Y]

  case class LoopOut[X, Y](
    src: WirePick[Y],
    tgt: WirePick[Y],
  ) extends Connector[X, Y]

  case class StudIn[X, Y](
    src: WirePick[X],
  ) extends Connector[X, Y]

  case class StudOut[X, Y](
    tgt: WirePick[Y],
  ) extends Connector[X, Y]
}
