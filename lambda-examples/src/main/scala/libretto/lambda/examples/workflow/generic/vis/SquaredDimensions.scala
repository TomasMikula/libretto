package libretto.lambda.examples.workflow.generic.vis

import libretto.lambda.examples.workflow.generic.vis.util.IntegralProportions
import scala.annotation.tailrec

private[vis] object SquaredDimensions extends Dimensions {
  case class Breadth(squaredValue: Long) {
    require(squaredValue > 0)

    lazy val doubleValue: Double =
      math.sqrt(squaredValue.toDouble)
  }

  case class Length(squaredValue: Long) {
    require(squaredValue >= 0)

    lazy val doubleValue: Double =
      math.sqrt(squaredValue.toDouble)
  }

  override type AspectRatio = (Length, Breadth)

  object Breadth extends BreadthModule {

    override def one: Breadth = Breadth(1L)

    override def max(a: Breadth, b: Breadth): Breadth =
      if a.squaredValue >= b.squaredValue then a else b

    override def cram(a: Breadth, b: Breadth): Breadth =
      // cram(a, b) = sqrt(a^2 + b^2)
      Breadth(a.squaredValue + b.squaredValue)

    override def divideProportionally(N: Int)(as: Breadth*): IntegralProportions =
      IntegralProportions.divideProportionally(N)(as.map(_.doubleValue).toArray)
  }

  object Length extends LengthModule {
    override def zero: Length = Length(0L)

    override def one: Length = Length(1L)

    override def cram(a: Length, b: Length): Length =
      // cram(a, b) = sqrt(a^2 + b^2)
      Length(a.squaredValue + b.squaredValue)

    override def divideProportionally(N: Int)(as: Length*): IntegralProportions =
      IntegralProportions.divideProportionally(N)(as.map(_.doubleValue).toArray)

    override def max(a: Length, b: Length): Length =
      if a.squaredValue >= b.squaredValue then a else b

  }

  object AspectRatio extends AspectRatioModule {
    override def apply(l: Length, b: Breadth): AspectRatio =
      (l, b)
  }

  extension (r: AspectRatio)
    override def scaleToFit(maxBreadth: Int, maxLength: Int): (Int, Int) =
      val (length, breadth) = r
      val (l, b) = (length.doubleValue, breadth.doubleValue)
      if
        (l * maxBreadth >= b * maxLength)
      then
        ((b / l * maxLength).toInt, maxLength)
      else
        (maxBreadth, (l / b * maxBreadth).toInt)
}
