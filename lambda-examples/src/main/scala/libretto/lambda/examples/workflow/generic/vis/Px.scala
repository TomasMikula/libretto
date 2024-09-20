package libretto.lambda.examples.workflow.generic.vis

opaque type Px = Int

object Px {
  def apply(n: Int): Px =
    require(n >= 0)
    n

  extension (x: Px)
    def pixels: Int = x
    def +(y: Px): Px = Px(x + y)
    def *(k: Int): Px = Px(x * k)
}
