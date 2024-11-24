package libretto.lambda.examples.workflow.generic.vis

opaque type Px = Int

object Px {
  def apply(n: Int): Px =
    require(n >= 0)
    n

  def max(a: Px, b: Px): Px =
    math.max(a, b)

  def min(a: Px, b: Px): Px =
    math.min(a, b)

  extension (x: Px)
    def pixels: Int = x
    def +(y: Px): Px = Px(x + y)
    def *(k: Int): Px = Px(x * k)
    def /(k: Int): Px = { require(k > 0); Px(x / k) }
    def halve: (Px, Px) = ((x+1)/2, x/2)

  extension (n: Int)
    def px: Px = Px(n)

  given Ordering[Px] = Ordering.Int
}
