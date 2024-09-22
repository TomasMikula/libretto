package libretto.lambda.examples.workflow.generic.vis

import libretto.lambda.examples.workflow.generic.vis.util.IntegralProportions

trait Dimensions {
  type Breadth
  type Length
  type AspectRatio

  val Breadth: BreadthModule
  val Length: LengthModule
  val AspectRatio: AspectRatioModule

  trait BreadthModule:
    def one: Breadth
    def max(a: Breadth, b: Breadth): Breadth
    def cram(a: Breadth, as: Breadth*): Breadth
    def divideProportionally(N: Int)(as: Breadth*): IntegralProportions

  trait LengthModule:
    def zero: Length
    def one: Length
    def max(a: Length, b: Length): Length
    def cram(as: Length*): Length
    def divideProportionally(N: Int)(as: Length*): IntegralProportions

  trait AspectRatioModule:
    def apply(l: Length, b: Breadth): AspectRatio

  extension (r: AspectRatio)
    def scaleToFit(maxBreadth: Int, maxLength: Int): (Int, Int)
}
