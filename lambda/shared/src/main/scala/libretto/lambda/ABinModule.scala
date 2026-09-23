package libretto.lambda

import libretto.lambda.util.{BiInjective, Exists, Functional2, Impossible3, Injective}
import libretto.lambda.util.Exists.Indeed

/** Used merely to front-load the initial type parameters of [[ABin]], exposing a more succinct type [[Construct]] on the inside. */
class ABinModule[<*>[_, _], T[_], Rel[_, _, _], F[_]](using
  Impossible3[[x, y, z] =>> T[x] =:= (y <*> z)],
  BiInjective[<*>],
  Injective[T],
) {

  /** Binary tree, viewed as "constructing" the root `R` from the leaves `As`. */
  opaque type Construct[As, R] = ABin[<*>, T, Rel, F, As, R]

  /** Like [[Construct]], but hides the root type of the tree, exposing only the leaves type `As`,
    * i.e. the intention from which the tree is built.
    */
  opaque type Intension[As] = ABin[<*>, T, Rel, F, As, ?]

  def wrap[As, R](r: ABin[<*>, T, Rel, F, As, R]): Construct[As, R] =
    r

  def apply[P, Q, R](
    root: Rel[P, Q, R],
  )[A, B](
    l: Construct[A, P],
    r: Construct[B, Q],
  ): Construct[A <*> B, R] =
    ABin.Branch(l, r, root)

  def atom[A](using a: F[A]): Construct[T[A], A] =
    ABin.Leaf(a)

  def lift[A, B, P](p: Rel[A, B, P])(using a: F[A], b: F[B]): Construct[T[A] <*> T[B], P] =
    apply(p)(atom[A], atom[B])

  object Intension {
    /** Witnesses that any type `A` with evidence `F[A]` builds a (singleton) tree. */
    given atom: [A] => F[A] => Intension[T[A]] =
      ABinModule.this.atom[A]

    given [A, B] => (a: Intension[A], b: Intension[B]) => (F Supports2 Rel, Rel Preserves2 F) => Intension[A <*> B] =
      summon[F Supports2 Rel]
        .apply(a.rootValue, b.rootValue) match
          case Indeed(p) => wrap(apply(p)(a, b))
  }

  extension [As, P](p: Construct[As, P]) {
    def unwrap: ABin[<*>, T, Rel, F, As, P] = p

    def rootValue(using Rel Preserves2 F): F[P] =
      p.rootValue

    def ^[Bs, Q](q: Construct[Bs, Q])(using
      ev1: F Supports2 Rel,
      ev2: Rel Preserves2 F,
    ): Exists[[R] =>> (Construct[As <*> Bs, R], Rel[P, Q, R])] =
      ev1(p.rootValue, q.rootValue) match
        case Indeed(rel) => Indeed((apply(rel)(p, q), rel))

    infix def uniq[Q](q: Construct[As, Q])(using
      Functional2[Rel],
    ): P =:= Q =
      ABin.uniq(p, q)
  }

  extension [As](as: Intension[As]) {
    def reveal: Exists[[R] =>> Construct[As, R]] =
      Indeed(as)
  }
}
