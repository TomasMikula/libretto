package libretto.lambda.examples.workflow.generic.vis

enum Color:
  case RGB private[Color](r: Int, g: Int, b: Int)
  case RGBA private[Color](r: Int, g: Int, b: Int, a: Double)
  case Black
  case White
  case Red
  case Green
  case Blue
  case Cyan
  case Magenta
  case Yellow

object Color:
  def rgb(r: Int, g: Int, b: Int): Color =
    require(r >= 0 && r < 256)
    require(g >= 0 && r < 256)
    require(b >= 0 && r < 256)
    Color.RGB(r, g, b)

  def rgba(r: Int, g: Int, b: Int, a: Double): Color =
    require(r >= 0 && r < 256)
    require(g >= 0 && r < 256)
    require(b >= 0 && r < 256)
    require(a >= 0.0 && a <= 1.0)
    Color.RGBA(r, g, b, a)