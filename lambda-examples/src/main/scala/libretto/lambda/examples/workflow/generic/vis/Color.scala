package libretto.lambda.examples.workflow.generic.vis

enum Color:
  case Black
  case White
  case Red
  case RGB private[Color](r: Int, g: Int, b: Int)

object Color:
  def rgb(r: Int, g: Int, b: Int): Color =
    require(r >= 0 && r < 256)
    require(g >= 0 && r < 256)
    require(b >= 0 && r < 256)
    Color.RGB(r, g, b)