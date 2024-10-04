package libretto.lambda.examples.workflow.generic.vis

sealed trait Connector[X, Y] {
  def style: Connector.Style
  def styled(style: Connector.Style): Connector[X, Y]

  def fill(color: Color): Connector[X, Y] =
    styled(this.style.copy(fill = color))
}

object Connector {
  case class Across[X, Y](
    src: WirePick[X],
    tgt: WirePick[Y],
    style: Connector.Style = Connector.Style.default,
  ) extends Connector[X, Y] {
    override def styled(style: Style): Connector[X, Y] = copy(style = style)
  }

  case class StudIn[X, Y](
    src: WirePick[X],
    style: Connector.Style = Connector.Style.default,
  ) extends Connector[X, Y] {
    override def styled(style: Style): Connector[X, Y] = copy(style = style)
  }

  case class StudOut[X, Y](
    tgt: WirePick[Y],
    style: Connector.Style = Connector.Style.default,
  ) extends Connector[X, Y] {
    override def styled(style: Style): Connector[X, Y] = copy(style = style)
  }

  case class Style(
    fill: Color,
  )

  object Style {
    def default: Style = Style(Color.Black)
  }
}
