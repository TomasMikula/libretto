package libretto.lambda

import libretto.lambda.util.Exists
import libretto.lambda.util.Exists.Indeed

/** Used merely to front-load the initial type parameters of [[ABin]], exposing a more succinct type [[Construct]] on the inside. */
class ABinModule[<*>[_, _], T[_], Rel[_, _, _], F[_]] {

  /** Binary tree, viewed as "constructing" the root `R` from the leaves `As`. */
  opaque type Construct[As, R] = ABin[<*>, T, Rel, F, As, R]

  def wrap[As, R](r: ABin[<*>, T, Rel, F, As, R]): Construct[As, R] =
    r

  def apply[A, B, P, Q, R](
    l: Construct[A, P],
    r: Construct[B, Q],
    combine: Rel[P, Q, R],
  ): Construct[A <*> B, R] =
    ABin.Branch(l, r, combine)

  extension [As, P](p: Construct[As, P]) {
    def unwrap: ABin[<*>, T, Rel, F, As, P] = p

    def rootValue(using Rel Preserves2 F): F[P] =
      p.rootValue

    def ^[Bs, Q](q: Construct[Bs, Q])(using
      ev1: F Supports2 Rel,
      ev2: Rel Preserves2 F,
    ): Exists[[R] =>> (Construct[As <*> Bs, R], Rel[P, Q, R])] =
      ev1(p.rootValue, q.rootValue) match
        case Indeed(rel) => Indeed((apply(p, q, rel), rel))
  }
}
