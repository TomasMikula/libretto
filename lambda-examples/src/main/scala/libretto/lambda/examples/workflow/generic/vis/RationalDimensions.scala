package libretto.lambda.examples.workflow.generic.vis

private[vis] object RationalDimensions extends Dimensions {
  import Dimensions.*

  /** Breadth, in abstract units. Must be positive. */
  override final case class Breadth(
    value: PositiveRational,
  )

  object Breadth extends BreadthModule {
    override val one = Breadth(PositiveRational.One)

    def max(a: Breadth, b: Breadth): Breadth =
      if a.value >= b.value
      then a
      else b

    override def cram(a: Breadth, b: Breadth): Breadth =
      Breadth(cramRationals(a.value, b.value))

    override def divideProportionally(N: Int)(a: Breadth, b: Breadth): IntegralProportions =
      require(N >= 0)
      divideByRationals(N)(a.value, b.value)
  }

  enum Length {
    case Zero
    case Positive(value: PositiveRational)

    def +(that: Length): Length =
      (this, that) match
        case (Zero, b) => b
        case (a, Zero) => a
        case (Positive(a), Positive(b)) => Positive(a + b)

    def *(b: PositiveRational): Length =
      this match
        case Zero => Zero
        case Positive(a) => Positive(a * b)

    def *(b: Int): Length =
      this * PositiveRational(b, 1)

    def /(b: PositiveRational): Length =
      this match
        case Zero => Zero
        case Positive(a) => Positive(a / b)

    def /(b: Int): Length =
      this / PositiveRational(b, 1)

    def toDouble: Double =
      this match
        case Zero => 0.0
        case Positive(value) => value.toDouble

  }

  object Length extends LengthModule {
    override val one = Positive(PositiveRational.One)
    override def zero = Zero

    override def max(a: Length, b: Length): Length =
      (a, b) match
        case (Zero, b) => b
        case (a, Zero) => a
        case (Positive(a), Positive(b)) => Positive(PositiveRational.max(a, b))

    override def cram(a: Length, b: Length): Length =
      (a, b) match
        case (Zero, b) => b
        case (a, Zero) => a
        case (Positive(a), Positive(b)) => Positive(cramRationals(a, b))

    override def divideProportionally(N: Int)(a: Length, b: Length): IntegralProportions =
      require(N >= 0)

      (a, b) match
        case (Zero, Zero) =>
          val a1 = N / 2
          val a2 = N - a1
          IntegralProportions(scalingFactor = 1, List(a1, a2))
        case (Zero, _) =>
          IntegralProportions(scalingFactor = 1, List(0, N))
        case (_, Zero) =>
          IntegralProportions(scalingFactor = 1, List(N, 0))
        case (Positive(la), Positive(lb)) =>
          divideByRationals(N)(la, lb)
  }

  /** Length-to-breadth ratio. */
  enum AspectRatio:
    case Zero
    case Positive(value: PositiveRational)

    def scaleToFit(maxBreadth: Int, maxLength: Int): (Int, Int) =
      this match
        case Zero =>
          (maxBreadth, 0)
        case Positive(r) =>
          if r > PositiveRational(maxLength, maxBreadth)
          then ((PositiveRational(maxLength, 1L) / r).roundToInt, maxLength)
          else (maxBreadth, (r * PositiveRational(maxBreadth, 1L)).roundToInt)


  object AspectRatio extends AspectRatioModule:
    def apply(l: Length, w: Breadth): AspectRatio =
      l match
        case Length.Zero        => Zero
        case Length.Positive(l) => Positive(l / w.value)

  extension (r: AspectRatio)
    override def scaleToFit(maxBreadth: Int, maxLength: Int): (Int, Int) =
      r match
        case AspectRatio.Zero =>
          (maxBreadth, 0)
        case AspectRatio.Positive(r) =>
          if r > PositiveRational(maxLength, maxBreadth)
          then ((r.invert * maxLength).roundToInt, maxLength)
          else (maxBreadth, (r * maxBreadth).roundToInt)


  private val SqueezeRatio =
    PositiveRational(3, 4)

  private def cramRationals(a: PositiveRational, b: PositiveRational): PositiveRational =
    (a + b) * SqueezeRatio

  private def divideByRationals(N: Int)(a: PositiveRational, b: PositiveRational): IntegralProportions =
    val c = a + b
    val k = ((a / c) * N).roundToInt
    val l = N - k
    IntegralProportions(scalingFactor = 1, sizes = List(k, l))
}
