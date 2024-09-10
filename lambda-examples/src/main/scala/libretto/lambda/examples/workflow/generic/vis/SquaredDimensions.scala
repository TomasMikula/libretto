package libretto.lambda.examples.workflow.generic.vis

import libretto.lambda.examples.workflow.generic.vis.Dimensions.IntegralProportions
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

    override def divideProportionally(N: Int)(a: Breadth, b: Breadth): IntegralProportions =
      divideDoublesProportionally(N)(a.doubleValue, b.doubleValue)
  }

  object Length extends LengthModule {
    override def zero: Length = Length(0L)

    override def one: Length = Length(1L)

    override def cram(a: Length, b: Length): Length =
      // cram(a, b) = sqrt(a^2 + b^2)
      Length(a.squaredValue + b.squaredValue)

    override def divideProportionally(N: Int)(a: Length, b: Length): IntegralProportions =
      require(N > 0)

      (a.squaredValue, b.squaredValue) match
        case (0L, 0L) =>
          val k = if N == 1 then 2 else 1
          val na = k*N / 2
          val nb = k*N - na
          IntegralProportions(k, List(na, nb))
        case (_, 0L) =>
          IntegralProportions(1, List(N, 0))
        case (0L, _) =>
          IntegralProportions(1, List(0, N))
        case (_, _) =>
          divideDoublesProportionally(N)(a.doubleValue, b.doubleValue)

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

  private def divideDoublesProportionally(N: Int)(a: Double, b: Double): IntegralProportions =
    require(N > 0)
    require(a > 0)
    require(b > 0)
    val ra = a / (a + b)
    assert(ra > 0.0)
    assert(ra < 1.0)
    val na = N * ra

    @tailrec def go(k: Int): IntegralProportions =
      val ma = (k * na).toInt
      val mb = k*N - ma
      if
        (ma > 0 && mb > 0)
      then
        IntegralProportions(k, List(ma, mb))
      else
        go(k + 1)

    go(1)
}
