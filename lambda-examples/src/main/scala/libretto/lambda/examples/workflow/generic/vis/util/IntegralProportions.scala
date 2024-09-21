package libretto.lambda.examples.workflow.generic.vis.util

import scala.annotation.tailrec

case class IntegralProportions(
  scalingFactor: Int,
  sizes: List[Int],
) {
  require(scalingFactor > 0)
  require(sizes.forall(_ >= 0))
}

object IntegralProportions {
  def divideProportionally(N: Int)(as: Array[Double]): IntegralProportions = {
    require(N > 0)
    require(as.forall(_ >= 0.0))
    val n = as.length
    val (sorted, perm) = Permutation.sort(as)
    val i = sorted.indexWhere(_ > 0.0)
    val (scale, sortedRes) =
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

    val res = perm.unpermute(sortedRes).to[List]
    IntegralProportions(scale, res)
  }
}
