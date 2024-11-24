package libretto.lambda.examples.workflow.generic.vis

/** Style applied to a nested node based on it's position in its parent. */
final case class AmbientStyle(
  background: Option[Color],
)

object AmbientStyle {
  val empty: AmbientStyle =
    AmbientStyle(background = None)

  def background(fill: Color): AmbientStyle =
    AmbientStyle(background = Some(fill))

  def leftOf[∙[_, _]](op: OpTag[∙]): AmbientStyle =
    op match
      case OpTag.Sum => background(StyleDefs.ColorCaseLeft)
      case OpTag.Pair => empty

  def rightOf[∙[_, _]](op: OpTag[∙]): AmbientStyle =
    op match
      case OpTag.Sum => background(StyleDefs.ColorCaseRight)
      case OpTag.Pair => empty

  def nthOf[Wrap[_]](op: OpTag[Wrap], n: Int): AmbientStyle =
    op match
      case OpTag.Enum =>
        val color =
          if n % 2 == 0
            then StyleDefs.ColorCaseLeft
            else StyleDefs.ColorCaseRight
        background(color)
      case _ =>
        empty
}
