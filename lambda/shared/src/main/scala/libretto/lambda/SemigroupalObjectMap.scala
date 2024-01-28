package libretto.lambda

import libretto.lambda.util.Functional

trait SemigroupalObjectMap[|*|[_, _], <*>[_, _], F[_, _]]
  extends PairwiseRel[|*|, <*>, F]
     with Functional[F]
