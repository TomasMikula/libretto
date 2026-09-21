package libretto.lambda

import libretto.lambda.util.{BiInjective, Functional2, Impossible3, Injective, TypeEq}
import libretto.lambda.util.TypeEq.Refl

class ProppedArrowModule[->[_, _], <*>[_, _], T[_], Rel[_, _, _], F[_]] {
  import ProppedArrowModule.*

  opaque type -×>[As, Bs] <: ProppedArrow[->, <*>, T, Rel, F, As, Bs] =
    ProppedArrow[->, <*>, T, Rel, F, As, Bs]

  def apply(using abin: ABinModule[<*>, T, Rel, F])[As, Bs, P, Q](
    p: abin.Construct[As, P],
    q: abin.Construct[Bs, Q],
  )(
    f: P -> Q,
  ): (As -×> Bs) =
    ProppedArrow.Impl(p.unwrap, q.unwrap, f)

  def lift[A: F, B: F](f: A -> B): T[A] -×> T[B] =
    ProppedArrow.Impl(ABin.leaf, ABin.leaf, f)
}

object ProppedArrowModule {

  sealed trait ProppedArrow[->[_, _], <*>[_, _], T[_], Rel[_, _, _], F[_], As, Bs] {
    type Src
    type Tgt

    def underlying: Src -> Tgt

    def src(using abin: ABinModule[<*>, T, Rel, F]): abin.Construct[As, Src] = abin.wrap(src)
    def tgt(using abin: ABinModule[<*>, T, Rel, F]): abin.Construct[Bs, Tgt] = abin.wrap(tgt)

    protected def src: ABin[<*>, T, Rel, F, As, Src]
    protected def tgt: ABin[<*>, T, Rel, F, Bs, Tgt]

    protected def extract[A, B](
      a: ABin[<*>, T, Rel, F, As, A],
      b: ABin[<*>, T, Rel, F, Bs, B],
    )(using
      Impossible3[[x, y, z] =>> T[x] =:= (y <*> z)],
      BiInjective[<*>],
      Injective[T],
      Functional2[Rel],
    ): A -> B

    protected def >[Cs](that: ProppedArrow[->, <*>, T, Rel, F, Bs, Cs])(using
      Impossible3[[x, y, z] =>> T[x] =:= (y <*> z)],
      BiInjective[<*>],
      Injective[T],
      Functional2[Rel],
      Semigroupoid[->],
    ): ProppedArrow[->, <*>, T, Rel, F, As, Cs]
  }

  private object ProppedArrow {
    case class Impl[->[_, _], <*>[_, _], T[_], Rel[_, _, _], F[_], As, Bs, P, Q](
      p: ABin[<*>, T, Rel, F, As, P],
      q: ABin[<*>, T, Rel, F, Bs, Q],
      f: P -> Q,
    ) extends ProppedArrow[->, <*>, T, Rel, F, As, Bs] {
      override type Src = P
      override type Tgt = Q

      override def underlying: Src -> Tgt = f
      override def src: ABin[<*>, T, Rel, F, As, P] = p
      override def tgt: ABin[<*>, T, Rel, F, Bs, Q] = q

      override def extract[A, B](
        a: ABin[<*>, T, Rel, F, As, A],
        b: ABin[<*>, T, Rel, F, Bs, B],
      )(using
        Impossible3[[x, y, z] =>> T[x] =:= (y <*> z)],
        BiInjective[<*>],
        Injective[T],
        Functional2[Rel],
      ): A -> B =
        (ABin.uniq(p, a), ABin.uniq(q, b)) match
          case (TypeEq(Refl()), TypeEq(Refl())) => f

      override def >[Cs](
        that: ProppedArrow[->, <*>, T, Rel, F, Bs, Cs],
      )(using
        Impossible3[[x, y, z] =>> T[x] =:= (y <*> z)],
        BiInjective[<*>],
        Injective[T],
        Functional2[Rel],
        Semigroupoid[->],
      ): ProppedArrow[->, <*>, T, Rel, F, As, Cs] =
        that match
          case Impl(q1, r, g) =>
            ABin.uniq(q, q1) match
              case TypeEq(Refl()) => Impl(p, r, f > g)
    }
  }

}
