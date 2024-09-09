package libretto.lambda.examples.workflow.generic.vis

// TODO: normalize (i.e. eliminate common divisors)
case class PositiveRational(
  numerator: Long,
  denominator: Long,
) {
  require(denominator > 0L)
  require(numerator   > 0L)

  def +(that: PositiveRational): PositiveRational =
    PositiveRational(
      this.numerator * that.denominator + that.numerator * this.denominator,
      this.denominator * that.denominator,
    )

  def *(that: PositiveRational): PositiveRational =
    PositiveRational(
      this.numerator * that.numerator,
      this.denominator * that.denominator,
    )

  def *(k: Int): PositiveRational =
    PositiveRational(
      numerator * k,
      denominator,
    )

  def /(that: PositiveRational): PositiveRational =
    println(s"Dividing $this by $that")
    PositiveRational(
      this.numerator * that.denominator,
      this.denominator * that.numerator,
    )

  def invert: PositiveRational =
    PositiveRational(denominator, numerator)

  infix def compare(that: PositiveRational): Int =
    val a = this.numerator * that.denominator
    val b = that.numerator * this.denominator
    a compare b

  def ==(that: PositiveRational): Boolean =
    (this compare that) == 0

  def >=(that: PositiveRational): Boolean =
    (this compare that) >= 0

  def >(that: PositiveRational): Boolean =
    (this compare that) > 0

  def <=(that: PositiveRational): Boolean =
    (this compare that) <= 0

  def <(that: PositiveRational): Boolean =
    (this compare that) < 0

  def toDouble: Double =
    numerator.toDouble / denominator

  def roundToInt: Int =
    math.round(toDouble).toInt

  override def toString: String =
    s"($numerator / $denominator)"
}

object PositiveRational {
  val One = PositiveRational(1L, 1L)

  def min(a: PositiveRational, b: PositiveRational): PositiveRational =
    if a <= b then a else b

  def max(a: PositiveRational, b: PositiveRational): PositiveRational =
    if a >= b then a else b
}