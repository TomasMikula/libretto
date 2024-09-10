package libretto.lambda.examples.workflow.generic.vis

trait Dimensions {
  import Dimensions.*

  type Breadth
  type Length
  type AspectRatio

  val Breadth: BreadthModule
  val Length: LengthModule
  val AspectRatio: AspectRatioModule

  trait BreadthModule:
    def one: Breadth
    def max(a: Breadth, b: Breadth): Breadth
    def cram(a: Breadth, b: Breadth): Breadth
    def divideProportionally(N: Int)(a: Breadth, b: Breadth): IntegralProportions

  trait LengthModule:
    def zero: Length
    def one: Length
    def max(a: Length, b: Length): Length
    def cram(a: Length, b: Length): Length
    def divideProportionally(N: Int)(a: Length, b: Length): IntegralProportions

  trait AspectRatioModule:
    def apply(l: Length, b: Breadth): AspectRatio

  extension (r: AspectRatio)
    def scaleToFit(maxBreadth: Int, maxLength: Int): (Int, Int)
}

object Dimensions {
  case class IntegralProportions(
    scalingFactor: Int,
    sizes: List[Int],
  ) {
    require(scalingFactor > 0)
    require(sizes.forall(_ >= 0))
  }
}
