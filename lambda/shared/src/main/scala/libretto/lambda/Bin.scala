package libretto.lambda

import libretto.lambda.util.{BiInjective, ClampEq, Exists, Injective, Masked, TypeEq}
import libretto.lambda.util.TypeEq.Refl

/**
 * Binary tree with leafs holding values of types `F[X]`, `F[Y]`, ...
 * The complete structure of the tree is expressed by the type `A`, using the tags for branches and leafs.
 *
 * @tparam <*> tag for branches, as it appears in `A`
 * @tparam T tag for leafs, as it appears in `A`
 * @tparam F value type of leafs. Each leaf holds a value of type `F[X]`, for some type `X`
 *   (but appears in `A` as `T[X]`).
 * @tparam A captures the complete structure of the tree
 */
sealed trait Bin[<*>[_, _], T[_], F[_], A] {
  import Bin.*

  def <*>[B](that: Bin[<*>, T, F, B]): Bin[<*>, T, F, A <*> B] =
    Branch(this, that)

  def mask: Masked[Bin[<*>, T, F, _], A] =
    Masked(this)

  def getValue[V](using
    leafIsNotBranch: [x, y, z] => (T[x] =:= (y <*> z)) => Nothing,
    T: Injective[T],
    ev: A =:= T[V],
  ): F[V] =
    ev match { case TypeEq(Refl()) => Bin.valueOf(this) }

  def mapLeafs[G[_]](f: [x] => F[x] => G[x]): Bin[<*>, T, G, A] =
    this match {
      case Leaf(a)      => Leaf(f(a))
      case Branch(l, r) => Branch(l.mapLeafs(f), r.mapLeafs(f))
    }

  def relabelLeafs[U[_], Tr[_, _]](
    leafTr: [X] => Unit => Tr[T[X], U[X]],
    parTr: [A1, A2, B1, B2] => (tr1: Tr[A1, B1], tr2: Tr[A2, B2]) => Tr[A1 <*> A2, B1 <*> B2],
  ): Exists[[B] =>> (Tr[A, B], Bin[<*>, U, F, B])] =
    this match
      case l: Leaf[p, t, f, a] =>
        Exists((leafTr[a](()), Leaf(l.value)))
      case b: Branch[p, t, f, a1, a2] =>
        (b.l.relabelLeafs[U, Tr](leafTr, parTr), b.r.relabelLeafs[U, Tr](leafTr, parTr)) match
          case (Exists.Some((tr1, b1)), Exists.Some((tr2, b2))) =>
            Exists((parTr(tr1, tr2), Branch(b1, b2)))

  def relabelLeafs[U[_], Tr[_, _], B](
    tr: Tr[A, B],
    leafToLeaf: [X, UX] => Tr[T[X], UX] => (UX =:= U[X]),
  )(using
    rel: PairwiseRel[<*>, <*>, Tr],
  ): Bin[<*>, U, F, B] =
    this match
      case l: Leaf[p, t, f, a] =>
        leafToLeaf[a, B](tr) match { case TypeEq(Refl()) => Leaf(l.value) }
      case b: Branch[p, t, f, a1, a2] =>
        rel.unpair[a1, a2, B](tr) match {
          case t @ rel.Unpaired.Impl(tr1, tr2) =>
            Branch(
              b.l.relabelLeafs[U, Tr, t.X1](tr1, leafToLeaf),
              b.r.relabelLeafs[U, Tr, t.X2](tr2, leafToLeaf),
            )
        }

  def foldMap[G[_]](
    map: [x] => F[x] => G[T[x]],
  )(using
    G: Zippable[<*>, G],
  ): G[A] =
    foldMapWith(
      map,
      [x, y] => (gx: G[x], gy: G[y]) => G.zip(gx, gy),
    )

  def foldMapWith[G[_]](
    map: [x] => F[x] => G[T[x]],
    zip: [x, y] => (G[x], G[y]) => G[x <*> y],
  ): G[A] =
    this match {
      case Leaf(a)      => map(a)
      case Branch(l, r) => zip(l.foldMapWith(map, zip), r.foldMapWith(map, zip))
    }

  def foldMap0[B](
    map: [x] => F[x] => B,
    reduce: (B, B) => B,
  ): B = {
    type G[x] = B
    foldMapWith[G](map, [x, y] => (x: G[x], y: G[y]) => reduce(x, y))
  }

  def foldRight[B](b: B)(f: [x] => (F[x], B) => B): B =
    this match
      case Leaf(a) =>
        f(a, b)
      case Branch(l, r) =>
        val b1 = r.foldRight(b)(f)
        l.foldRight(b1)(f)

  def partition[G[_], H[_]](
    f: [x] => F[x] => Either[G[x], H[x]],
  )(using
    shuffle: Shuffle[<*>],
  ): Partitioned[G, H, shuffle.~⚬] = {
    import shuffle.~⚬
    import shuffle.~⚬.{assocLR, assocRL, fst, id, ix, ixi, par, snd, swap, xi}

    this match {
      case Leaf(a) =>
        f(a) match
          case Left(a)  => Partitioned.Left(Leaf(a))
          case Right(a) => Partitioned.Right(Leaf(a))
      case Branch(l, r) =>
        import Partitioned.{Both, Left, Right}
        import l.Partitioned.{Both as LBoth, Left as LLeft, Right as LRight}
        import r.Partitioned.{Both as RBoth, Left as RLeft, Right as RRight}

        (l.partition(f), r.partition(f)) match
          case (LLeft(lg),        RLeft(rg))        => Left(lg <*> rg)
          case (LLeft(lg),        RRight(rh))       => Both(lg, rh, id)
          case (LLeft(lg),        RBoth(rg, rh, t)) => Both(lg <*> rg, rh, assocLR > snd(t))
          case (LRight(lh),       RLeft(rg))        => Both(rg, lh, swap)
          case (LRight(lh),       RRight(rh))       => Right(lh <*> rh)
          case (LRight(lh),       RBoth(rg, rh, t)) => Both(rg, lh <*> rh, xi > snd(t))
          case (LBoth(lg, lh, s), RLeft(rg))        => Both(lg <*> rg, lh, ix > fst(s))
          case (LBoth(lg, lh, s), RRight(rh))       => Both(lg, lh <*> rh, assocRL > fst(s))
          case (LBoth(lg, lh, s), RBoth(rg, rh, t)) => Both(lg <*> rg, lh <*> rh, ixi > par(s, t))
    }
  }

  enum Partitioned[G[_], H[_], ~⚬[_, _]] {
    case Left(value: Bin[<*>, T, G, A])
    case Right(value: Bin[<*>, T, H, A])
    case Both[G[_], H[_], X, Y, ~⚬[_, _]](
      l: Bin[<*>, T, G, X],
      r: Bin[<*>, T, H, Y],
      f: (X <*> Y) ~⚬ A,
    ) extends Partitioned[G, H, ~⚬]
  }

  def deduplicateLeafs[->[_, _]](
    dup: [x] => F[x] => T[x] -> (T[x] <*> T[x]),
  )(using
    leafTest: ClampEq[F],
    shuffled: ShuffledModule[->, <*>],
  ): Exists[[X] =>> (Bin[<*>, T, F, X], shuffled.Shuffled[X, A])] =
    this match {
      case l @ Leaf(_) =>
        Exists((l, shuffled.id))
      case Branch(l, r) =>
        (l.deduplicateLeafs(dup), r.deduplicateLeafs(dup)) match
          case (Exists.Some((x1, f1)), Exists.Some((x2, f2))) =>
            (x1 mergeIn x2)(dup) match
              case Exists.Some((x, f)) =>
                Exists((x, f > shuffled.par(f1, f2)))
    }

  private infix def mergeIn[B, ->[_, _]](that: Bin[<*>, T, F, B])(
    dup: [x] => F[x] => T[x] -> (T[x] <*> T[x]),
  )(using
    leafTest: ClampEq[F],
    shuffled: ShuffledModule[->, <*>],
  ): Exists[[X] =>> (Bin[<*>, T, F, X], shuffled.Shuffled[X, A <*> B])] =
    (this mergeIn0 that)(dup) match {
      case MergeRes.Absorbed(x, f) =>
        Exists((x, f))
      case MergeRes.WithRemainder(x, r, f1, g) =>
        Exists((Branch(x, r), shuffled.fst(f1) > shuffled.pure(g)))
    }

  private infix def mergeIn0[B, ->[_, _]](that: Bin[<*>, T, F, B])(
    dup: [x] => F[x] => T[x] -> (T[x] <*> T[x]),
  )(using
    leafTest: ClampEq[F],
    shuffled: ShuffledModule[->, <*>],
  ): MergeRes[A, B, shuffled.shuffle.~⚬, shuffled.Shuffled] = {
    import MergeRes.{Absorbed, WithRemainder}
    import shuffled.{assocRL, fst, id, ix, lift, par, pure, swap, xi}
    import shuffled.shuffle.~⚬

    given shuffled.shuffle.type = shuffled.shuffle

    this match {
      case l: Leaf[br, t, f, a] =>
        that.find(l.value) match
          case that.FindRes.Total(TypeEq(Refl())) =>
            Absorbed(l, lift(dup(l.value)))
          case that.FindRes.Partial(r, f) =>
            WithRemainder(l, r, lift(dup(l.value)), ~⚬.assocLR > f.inSnd)
          case that.FindRes.NotFound() =>
            WithRemainder(this, that, id, ~⚬.id)
      case br: Branch[br, t, f, a1, a2] =>
        (br.l mergeIn0 that)(dup) match
          case br.l.MergeRes.Absorbed(p, f) =>
            Absorbed(Branch(p, br.r), f.inFst[a2] > ix)
          case br.l.MergeRes.WithRemainder(p, r, f1, g) =>
            (br.r mergeIn0 r)(dup) match
              case br.r.MergeRes.Absorbed(p1, f2) =>
                Absorbed(Branch(p, p1), par(f1, f2) > xi > pure(g).inSnd > assocRL > fst(swap))
              case br.r.MergeRes.WithRemainder(p1, r1, f2, g2) =>
                WithRemainder(Branch(p, p1), r1, par(f1, f2), ~⚬.assocLR > ~⚬.snd(g2) > ~⚬.xi > ~⚬.snd(g) > ~⚬.assocRL > ~⚬.fst(~⚬.swap))
    }
  }

  private enum MergeRes[A, B, -->[_, _], ==>[_, _]] {
    case Absorbed[P, A, B, -->[_, _], ==>[_, _]](
      p: Bin[<*>, T, F, P],
      f: P ==> (A <*> B),
    ) extends MergeRes[A, B, -->, ==>]

    case WithRemainder[P, Q, R, A, B, -->[_, _], ==>[_, _]](
      p: Bin[<*>, T, F, P],
      r: Bin[<*>, T, F, R],
      f1: P ==> Q,
      g: (Q <*> R) --> (A <*> B),
    ) extends MergeRes[A, B, -->, ==>]
  }

  /** Returns a tree with the least common superset of leaves
   * and projections to get back to each of the two inputs.
   */
  infix def union[B, ->[_, _]](that: Bin[<*>, T, F, B])(
    discardFst: [X, Y] => F[X] => (T[X] <*> Y) -> Y,
  )(using
    leafTest: ClampEq[F],
    shuffled: ShuffledModule[->, <*>],
  ): Exists[[P] =>> (
    Bin[<*>, T, F, P],
    shuffled.Shuffled[P, A],
    shuffled.Shuffled[P, B],
  )] =
    (this union0 that)(discardFst) match {
      case UnionRes.Absorbed(x, p1, p2) =>
        Exists((x, p1, p2))
      case UnionRes.WithRemainder(x, r, p1, p2) =>
        Exists((
          Branch(x, r),
          r.discardAll(discardFst).inSnd > p1,
          p2,
        ))
    }

  private infix def union0[B, ->[_, _]](that: Bin[<*>, T, F, B])(
    discardFst: [X, Y] => F[X] => (T[X] <*> Y) -> Y,
  )(using
    leafTest: ClampEq[F],
    shuffled: ShuffledModule[->, <*>],
  ): UnionRes[A, B, shuffled.Shuffled] = {
    import UnionRes.{Absorbed, WithRemainder}
    given shuffled.shuffle.type = shuffled.shuffle
    import shuffled.{assocLR, id, lift, par, pure}

    this match {
      case l: Leaf[br, t, f, a] =>
        that.find(l.value) match
          case that.FindRes.Total(TypeEq(Refl())) =>
            Absorbed(l, id, id)
          case that.FindRes.Partial(r, f) =>
            WithRemainder(l, r, id, pure(f))
          case that.FindRes.NotFound() =>
            WithRemainder(l, that, id, lift(discardFst(l.value)))
      case br: Branch[br, t, f, a1, a2] =>
        (br.l union0 that)(discardFst) match
          case br.l.UnionRes.Absorbed(p, p1, p2) =>
            Absorbed(Branch(p, br.r), p1.inFst, br.r.discardAll(discardFst).inSnd > p2)
          case br.l.UnionRes.WithRemainder(p, r, p1, p2) =>
            (br.r union0 r)(discardFst) match
              case br.r.UnionRes.Absorbed(q, q1, q2) =>
                Absorbed(Branch(p, q), par(p1, q1), q2.inSnd > p2)
              case br.r.UnionRes.WithRemainder(q, r, q1, q2) =>
                WithRemainder(Branch(p, q), r, par(p1, q1), assocLR > q2.inSnd > p2)
    }
  }

  private enum UnionRes[A, B, -->[_, _]] {
    case Absorbed[P, A, B, -->[_, _]](
      p: Bin[<*>, T, F, P],
      p1: P --> A,
      p2: P --> B,
    ) extends UnionRes[A, B, -->]

    case WithRemainder[P, R, A0, B0, A, B, -->[_, _]](
      p: Bin[<*>, T, F, P],
      r: Bin[<*>, T, F, R],
      p1: P --> A,
      p2: (P <*> R) --> B,
    ) extends UnionRes[A, B, -->]
  }

  private def discardAll[->[_, _]](discardFst: [X, Y] => F[X] => (T[X] <*> Y) -> Y): DiscardingAll[->] =
    DiscardingAll(discardFst)

  private class DiscardingAll[->[_, _]](discardFst: [X, Y] => F[X] => (T[X] <*> Y) -> Y) {
    def inSnd[P](using shuffled: ShuffledModule[->, <*>]): shuffled.Shuffled[P <*> A, P] = {
      Bin.this match {
        case Leaf(value) => shuffled.swap > shuffled.lift(discardFst(value))
        case Branch(l, r) => shuffled.assocRL > r.discardAll(discardFst).inSnd > l.discardAll(discardFst).inSnd
      }
    }
  }

  private def find[X](x: F[X])(using
    leafTest: ClampEq[F],
    shuffle: Shuffle[<*>],
  ): FindRes[A, X, shuffle.~⚬] = {
    import FindRes.*
    import shuffle.~⚬

    this match {
      case Leaf(a) =>
        leafTest.testEqual(a, x) match
          case Some(ev) => Total(ev.liftCo[T])
          case None     => NotFound()
      case Branch(l, r) =>
        l.find(x) match
          case l.FindRes.Total(TypeEq(Refl())) =>
            Partial(r, ~⚬.id)
          case l.FindRes.Partial(q, f) =>
            Partial(Branch(q, r), ~⚬.assocRL > f.inFst)
          case l.FindRes.NotFound() =>
            r.find(x) match
              case r.FindRes.Total(TypeEq(Refl())) =>
                Partial(l, ~⚬.swap)
              case r.FindRes.Partial(q, f) =>
                Partial(Branch(l, q), ~⚬.xi > ~⚬.snd(f))
              case r.FindRes.NotFound() =>
                NotFound()
    }
  }

  private enum FindRes[A, X, -->[_, _]] {
    case NotFound()
    case Total(ev: A =:= T[X])

    case Partial[R, A, X, -->[_, _]](
      remainder: Bin[<*>, T, F, R],
      f: (T[X] <*> R) --> A
    ) extends FindRes[A, X, -->]
  }
}

object Bin {
  case class Branch[<*>[_, _], T[_], F[_], A, B](l: Bin[<*>, T, F, A], r: Bin[<*>, T, F, B]) extends Bin[<*>, T, F, A <*> B]
  case class Leaf[<*>[_, _], T[_], F[_], A](value: F[A]) extends Bin[<*>, T, F, T[A]]

  def branchesOf[<*>[_, _], T[_], F[_], A, B](tree: Bin[<*>, T, F, A <*> B])(using
    leafIsNotBranch: [x, y, z] => (T[x] =:= (y <*> z)) => Nothing,
  )(using
    BiInjective[<*>],
  ): (Bin[<*>, T, F, A], Bin[<*>, T, F, B]) =
    tree.mask.visit[(Bin[<*>, T, F, A], Bin[<*>, T, F, B])](
      [X] => (tree: Bin[<*>, T, F, X], ev: X =:= (A <*> B)) =>
        tree match {
          case t: Branch[br, lf, f, a, b] =>
            (summon[(a <*> b) =:= X] andThen ev) match
              case BiInjective[<*>](TypeEq(Refl()), TypeEq(Refl())) =>
                (t.l, t.r)
          case _: Leaf[br, lf, f, v] =>
            leafIsNotBranch[v, A, B](ev)
        }
    )

  def valueOf[<*>[_, _], T[_], F[_], A](tree: Bin[<*>, T, F, T[A]])(using
    leafIsNotBranch: [x, y, z] => (T[x] =:= (y <*> z)) => Nothing,
  )(using
    Injective[T],
  ): F[A] =
    tree.mask.visit[F[A]](
      [X] => (tree: Bin[<*>, T, F, X], ev: X =:= T[A]) =>
        tree match
          case l: Leaf[br, t, f, x] =>
            (summon[T[x] =:= X] andThen ev) match
              case Injective[T](TypeEq(Refl())) =>
                l.value
          case _: Branch[br, t, f, a, b] => leafIsNotBranch[A, a, b](ev.flip)
    )

  given [<*>[_, _], T[_], F[_]](using
    leafIsNotBranch: [x, y, z] => (T[x] =:= (y <*> z)) => Nothing,
  )(using
    BiInjective[<*>],
  ): StrongZippable[<*>, Bin[<*>, T, F, _]] with {
    override def zip[A, B](a: Bin[<*>, T, F, A], b: Bin[<*>, T, F, B]): Bin[<*>, T, F, A <*> B] =
      Branch(a, b)

    override def unzip[A, B](ab: Bin[<*>, T, F, A <*> B]): (Bin[<*>, T, F, A], Bin[<*>, T, F, B]) =
      branchesOf(ab)
  }
}
