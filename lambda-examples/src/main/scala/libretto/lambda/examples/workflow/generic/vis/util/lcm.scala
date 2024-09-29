package libretto.lambda.examples.workflow.generic.vis.util

/** Returns `(i, j, m)`, such that `a * i = b * j = m`. */
def leastCommonMultiple(a: Int, b: Int): (Int, Int, Int) = {
  require(a > 0)
  require(b > 0)
  val res @ (i, j, m) =
    if (a == b)
      (1, 1, a)
    else if (a > b)
      leastCommonMultiple(a, 1, a, b, 1, b)
    else
      val (j, i, m) = leastCommonMultiple(b, 1, b, a, 1, a)
      (i, j, m)
  assert(a * i == m)
  assert(b * j == m)
  res
}

private def leastCommonMultiple(a: Int, i: Int, ai: Int, b: Int, j: Int, bj: Int): (Int, Int, Int) =
  require(a > b)
  require(ai > bj)
  val k = (ai - bj) / b
  val bj1 = (j + k) * b
  if (bj1 == ai)
    (i, j+k, ai)
  else
    assert(bj1 < ai)
    assert(bj1 + b > ai)
    leastCommonMultiple(a, i+1, ai + a, b, j+k, bj1)
