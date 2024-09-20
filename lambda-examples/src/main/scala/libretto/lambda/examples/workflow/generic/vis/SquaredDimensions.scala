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

    override def divideProportionally(N: Int)(as: Breadth*): IntegralProportions =
      divideDoublesProportionally(N)(as.map(_.doubleValue).toArray)
  }

  object Length extends LengthModule {
    override def zero: Length = Length(0L)

    override def one: Length = Length(1L)

    override def cram(a: Length, b: Length): Length =
      // cram(a, b) = sqrt(a^2 + b^2)
      Length(a.squaredValue + b.squaredValue)

    override def divideProportionally(N: Int)(as: Length*): IntegralProportions =
      divideDoublesProportionally(N)(as.map(_.doubleValue).toArray)

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

  private def divideDoublesProportionally(N: Int)(as: Array[Double]): IntegralProportions = {
    require(N > 0)
    require(as.forall(_ >= 0.0))
    val n = as.length
    val (sorted, perm) = as.zipWithIndex.sortInPlaceBy(_._1).unzip
    val i = sorted.indexWhere(_ > 0.0)
    val (scale, res) =
      if (i == -1) {
        // all proportions are 0.0, divide equally
        val k = N / n
        val r = N - n*k
        val s = n - r
        val res: Array[Int] = new Array[Int](n)
        for (j <- 0 until r) { res(j) = k+1 }
        for (j <- r until n) { res(j) = k   }
        (1, res)
      } else {
        val min = sorted(i) * N
        val (k, kN) =
          if (min < 10.0) {
            val k = math.ceil(10.0/min).toInt
            (k, k*N)
          } else
            (1, N)

        val res = new Array[Int](n)
        for (j <- 0 until i) { res(j) = 0 }

        @tailrec
        def go(N: Int, from: Int): Unit = {
          require(from < n)
          if (from == n - 1)
            res(from) = N
          else
            val sum = sorted.slice(from, n).sum
            val mid = (from + n) / 2
            assert(mid > from)
            for (j <- from until mid) {
              res(j) = math.round(sorted(j) * N / sum).toInt
            }
            val allocated = res.slice(from, mid).sum
            assert(allocated < N)
            go(N - allocated, mid)
        }

        go(kN, i)
        (k, res)
      }

    // return to original order
    for (i <- 0 until n) {
      @tailrec
      def go(a: Int, tgtIdx: Int): Unit =
        val b = res(tgtIdx)
        res(tgtIdx) = a
        val nextTgt = perm(tgtIdx)
        perm(tgtIdx) = -1
        if (nextTgt != -1) {
          go(b, nextTgt)
        }
      val j = perm(i)
      if (j != -1) {
        perm(i) = -1
        go(res(i), j)
      }
    }

    IntegralProportions(scale, res.toList)
  }
}
