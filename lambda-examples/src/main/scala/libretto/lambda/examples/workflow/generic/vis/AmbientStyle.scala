package libretto.lambda.examples.workflow.generic.vis

/** Style information passed from an outer node to its nested nodes. */
final case class AmbientStyle(
  background: Option[Color],
  base: Option[AmbientStyle],
) {
  import AmbientStyle.empty

  infix def over(that: AmbientStyle): AmbientStyle =
    if (that == empty)
      this
    else if (this == empty)
      that
    else
      base match
        case None => copy(base = Some(that))
        case Some(base) => copy(base = Some(base over that))
}

object AmbientStyle {
  val empty: AmbientStyle =
    AmbientStyle(background = None, base = None)

  def background(fill: Color): AmbientStyle =
    AmbientStyle(background = Some(fill), base = None)

  def leftOf[∙[_, _]](op: OpTag[∙]): AmbientStyle =
    op match
      case OpTag.Sum => background(StyleDefs.ColorCaseLeft)
      case OpTag.Pair => empty

  def rightOf[∙[_, _]](op: OpTag[∙]): AmbientStyle =
    op match
      case OpTag.Sum => background(StyleDefs.ColorCaseRight)
      case OpTag.Pair => empty
}
