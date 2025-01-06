package libretto.lambda

import libretto.lambda.{Projection as P}
import libretto.lambda.util.{Applicative, BiInjective, Exists, TypeEq}
import libretto.lambda.util.TypeEq.Refl
import libretto.lambda.Projection.Proper

object Shuffled {
  type With[->[_, _], |*|[_, _], S <: Shuffle[|*|]] =
    Shuffled[->, |*|] {
      val shuffle: S
    }

  def apply[->[_, _], |*|[_, _]](sh: Shuffle[|*|])(using BiInjective[|*|]): Shuffled.With[->, |*|, sh.type] =
    new ShuffledImpl[->, |*|, sh.type](sh)

  def apply[->[_, _], |*|[_, _]](using BiInjective[|*|]): Shuffled[->, |*|] =
    Shuffled[->, |*|](new Shuffle[|*|])

  private class ShuffledImpl[->[_, _], |*|[_, _], S <: Shuffle[|*|]](
    override val shuffle: S,
  )(using
    BiInjective[|*|],
  ) extends Shuffled[->, |*|]
}

sealed abstract class Shuffled[->[_, _], |*|[_, _]](using BiInjective[|*|]) {
  val shuffle: Shuffle[|*|]
  import shuffle.{~⚬, Transfer, TransferOpt, zip as zipEq}

  def biInjectiveProduct: BiInjective[|*|] = summon

  sealed trait Shuffled[A, B] {
    infix def after[Z](that: Shuffled[Z, A]): Shuffled[Z, B]
    infix def thenShuffle[C](that: B ~⚬ C): Shuffled[A, C]
    infix def afterShuffle[Z](that: Z ~⚬ A): Shuffled[Z, B]
    def foldMap[->>[_, _]](f: [x, y] => (x -> y) => (x ->> y))(using SymmetricSemigroupalCategory[->>, |*|]): A ->> B
    def inFst[Y]: Shuffled[A |*| Y, B |*| Y]
    def inSnd[X]: Shuffled[X |*| A, X |*| B]
    def unconsSome: UnconsSomeRes[A, B]

    def sweepL[F[_], ->>[_, _]](
      a: F[A],
      f: [t, u] => (F[t], t -> u) => (t ->> u, F[u]),
    )(using
      tgt: libretto.lambda.Shuffled.With[->>, |*|, shuffle.type],
      F: StrongZippable[|*|, F],
    ): (tgt.Shuffled[A, B], F[B])

    def traverse[G[_], ->>[_, _]](
      f: [t, u] => (t -> u) => G[t ->> u],
    )(using
      tgt: libretto.lambda.Shuffled.With[->>, |*|, shuffle.type],
      G: Applicative[G],
    ): G[tgt.Shuffled[A, B]]

    def translate[->>[_, _], <*>[_, _], F[_, _], S](
      fa: F[A, S],
      om: SemigroupalObjectMap[|*|, <*>, F],
      am: ArrowMap[->, ->>, F],
    )(using
      tgt: libretto.lambda.Shuffled[->>, <*>],
    ): Exists[[T] =>> (tgt.Shuffled[S, T], F[B, T])]

    def >[C](that: Shuffled[B, C]): Shuffled[A, C] =
      that after this

    def fold(using SymmetricSemigroupalCategory[->, |*|]): A -> B =
      foldMap[->]([x, y] => (f: x -> y) => f)

    def foldMapA[G[_], ->>[_, _]](
      f: [t, u] => (t -> u) => G[t ->> u],
    )(using
      G: Applicative[G],
      cat: SymmetricSemigroupalCategory[->>, |*|],
    ): G[A ->> B] =
      this
        .traverse[G, ->>](f)(using libretto.lambda.Shuffled(shuffle), G)
        .map(_.fold)

    def at[F[_]](f: Focus[|*|, F]): Shuffled[F[A], F[B]] =
      f match {
        case Focus.Id()    => this
        case Focus.Fst(f1) => this.at(f1).inFst
        case Focus.Snd(f2) => this.at(f2).inSnd
      }

    def chaseFw[F[_], X](i: Focus[|*|, F])(using A =:= F[X]): ChaseFwRes[F, X, B]

    def chaseBw[G[_], X](i: Focus[|*|, G])(using B =:= G[X]): ChaseBwRes[A, G, X]

    def project[C](
      p: Projection[|*|, B, C],
      f: [X, Y, Z] => (X -> Y, Projection[|*|, Y, Z]) => ProjectRes[X, Z],
    ): ProjectRes[A, C]

    /** Extracts the maximum forest-shaped prefix at the given position. */
    def takeLeadingForestAt[F[_], X](
      pos: Focus[|*|, F],
    )(using
      ev: A =:= F[X],
    ): Exists[[Y] =>> (AForest[->, |*|, X, Y], Shuffled[F[Y], B])] =
      takeLeadingForestAtWhile[F, X, ->](
        pos,
        [x, y] => (f: x -> y) => Some(f),
      )

    /** Extracts the maximum forest-shaped prefix
     * at the given position satisfying the given predicate.
     */
    def takeLeadingForestAtWhile[F[_], X, ->>[_, _]](
      pos: Focus[|*|, F],
      pred: [x, y] => (x -> y) => Option[x ->> y],
    )(using
      ev: A =:= F[X],
    ): Exists[[Y] =>> (AForest[->>, |*|, X, Y], Shuffled[F[Y], B])] =
      chaseFw(pos) match
        case ChaseFwRes.Transported(_, _) =>
          Exists((AForest.Empty(), this.from(using ev.flip)))
        case sp: ChaseFwRes.Split[f, x, x1, x2, b] =>
          sp.ev match { case TypeEq(Refl()) =>
            type F1[T] = F[T |*| x2]
            takeLeadingForestAtWhile[F1, x1, ->>](pos compose Focus.fst, pred) match
              case res1 @ Exists.Some((f1, s1)) =>
                type F2[T] = F[res1.T |*| T]
                s1.takeLeadingForestAtWhile[F2, x2, ->>](pos compose Focus.snd, pred) match
                  case Exists.Some((f2, s2)) =>
                    Exists((AForest.par(f1, f2), s2))
          }
        case r: ChaseFwRes.FedTo[f, x, v, w, g, b] =>
          r.v match
            case Focus.Id() =>
              pred(r.f) match
                case None =>
                  Exists((AForest.Empty(), this.from(using ev.flip)))
                case Some(f0) =>
                  r.post.takeLeadingForestAtWhile[g, w, ->>](r.g, pred) match
                    case Exists.Some((f1, s)) =>
                      Exists.Some((AForest.Node(f0, f1), s.after(r.pre.apply)))
            case Focus.Fst(_) | Focus.Snd(_) =>
              Exists((AForest.Empty(), this.from(using ev.flip)))

    def to[C](using ev: B =:= C): Shuffled[A, C] =
      ev.substituteCo(this)

    def from[Z](using ev: Z =:= A): Shuffled[Z, B] =
      ev.substituteContra[Shuffled[_, B]](this)
  }

  sealed trait Permeable[A, B] extends Shuffled[A, B]

  case class Impermeable[A, X, Y, B](l: A ~⚬ X, m: Plated[X, Y], r: Y ~⚬ B) extends Shuffled[A, B] {
    override def after[Z](that: Shuffled[Z, A]): Impermeable[Z, ?, ?, B] =
      (that thenShuffle l) match {
        case Impermeable(i, j, k) =>
          Impermeable(i, Plated.Sandwich(j, k, m), r)
        case k: Permeable[Z, X] =>
          (m afterPermeable k) match
            case Plated.Preshuffled(k, m) => Impermeable(k, m, r)
      }

    override def >[C](that: Shuffled[B, C]): Impermeable[A, ?, ?, C] =
      (that afterShuffle r) match {
        case Impermeable(i, j, k) =>
          Impermeable(l, Plated.Sandwich(m, i, j), k)
        case k: Permeable[Y, C] =>
          (m thenPermeable k) match
            case Plated.Postshuffled(m, s) => Impermeable(l, m, s)
      }

    override def thenShuffle[C](s: B ~⚬ C): Impermeable[A, X, Y, C] =
      Impermeable(l, m, r > s)

    override def afterShuffle[Z](k: Z ~⚬ A): Shuffled[Z, B] =
      Impermeable(k > l, m, r)

    override def foldMap[->>[_, _]](
      tr: [x, y] => (x -> y) => (x ->> y),
    )(using
      ev: SymmetricSemigroupalCategory[->>, |*|],
    ): A ->> B = {
      val (f, g, h) = (l.fold, m.foldMap(tr), r.fold)
      ev.andThen(f, ev.andThen(g, h))
    }

    override def inFst[Q]: Shuffled[A |*| Q, B |*| Q] =
      swap > inSnd[Q] > swap

    override def inSnd[P]: Shuffled[P |*| A, P |*| B] =
      SemiObstructed(~⚬.snd(l), m, r, TransferOpt.None())

    override def unconsSome: UnconsSomeRes[A, B] =
      m.unconsSome match
        case c: Plated.UnconsSomeRes.Cons[f, v, w, y] =>
          UnconsSomeRes.Cons[A, f, v, w, B](l, c.i, c.f, c.post thenShuffle r)

    override def translate[->>[_, _], <*>[_, _], F[_, _], S](
      fa: F[A, S],
      om: SemigroupalObjectMap[|*|, <*>, F],
      am: ArrowMap[->, ->>, F],
    )(using
      tgt: libretto.lambda.Shuffled[->>, <*>],
    ): Exists[[T] =>> (tgt.Shuffled[S, T], F[B, T])] = {
      l.translate[<*>, F, S](fa)(om, tgt.shuffle) match
        case Exists.Some((l1, fx)) =>
          m.translate(fx, om, am) match
            case Exists.Some((m1, fy)) =>
              r.translate(fy)(om, tgt.shuffle) match
                case Exists.Some((r1, fb)) =>
                  Exists((tgt.Impermeable(l1, m1, r1), fb))
    }

    override def traverse[G[_], ->>[_,_]](
      f: [t, u] => (t -> u) => G[t ->> u]
    )(using
      tgt: libretto.lambda.Shuffled.With[->>, |*|, shuffle.type],
      G: Applicative[G],
    ): G[tgt.Shuffled[A, B]] =
      m.traverse(f).map { m1 => tgt.Impermeable(l, m1, r) }

    override def sweepL[F[_], ->>[_,_]](
      a: F[A],
      f: [t, u] => (F[t], t -> u) => (t ->> u, F[u]),
    )(using
      tgt: libretto.lambda.Shuffled.With[->>, |*|, shuffle.type],
      F: StrongZippable[|*|, F],
    ): (tgt.Shuffled[A, B], F[B]) = {
      val x: F[X] = l(a)
      val (m1, y) = m.sweepL[F, ->>](x, f)
      val b = r(y)
      (tgt.Impermeable(l, m1, r), b)
    }

    override def project[C](
      p: Projection[|*|, B, C],
      f: [P, Q, R] => (P -> Q, Projection[|*|, Q, R]) => ProjectRes[P, R],
    ): ProjectRes[A, C] =
      r.project(p) match
        case ~⚬.ProjectRes.Projected(py, r1) =>
          m.project(py, f) match
            case ProjectRes.Projected(px, m1) =>
              l.project(px) match
                case ~⚬.ProjectRes.Projected(pa, l1) =>
                  ProjectRes.Projected(pa, Pure(l1) > m1 > Pure(r1))

    override def chaseBw[G[_], T](i: Focus[|*|, G])(using ev: B =:= G[T]): ChaseBwRes[A, G, T] =
      r.chaseBw(i) match
        case tr: ~⚬.ChaseBwRes.Transported[y, f, g, t] =>
          m.chaseBw[f, T](tr.s.focusIn)(using tr.ev)
            .after(Pure(l))
            .andThen(Punched.pure(tr.s))
        case ~⚬.ChaseBwRes.Split(ev) =>
          ChaseBwRes.Split(ev)

    override def chaseFw[F[_], T](i: Focus[|*|, F])(using A =:= F[T]): ChaseFwRes[F, T, B] =
      l.chaseFw(i) match
        case tr: ~⚬.ChaseFwRes.Transported[f, t, g, x] =>
          m.chaseFw[g, T](tr.s.focusOut)(using tr.ev.flip)
            .andThen(Pure(r))
            .after(Punched.pure(tr.s))
        case ~⚬.ChaseFwRes.Split(ev) =>
          ChaseFwRes.Split(ev)
  }

  case class Pure[A, B](s: A ~⚬ B) extends Permeable[A, B] {
    override def after[Z](that: Shuffled[Z, A]): Shuffled[Z, B] =
      that thenShuffle s

    override def thenShuffle[C](t: B ~⚬ C): Pure[A, C] =
      Pure(s > t)

    override def afterShuffle[Z](r: Z ~⚬ A): Shuffled[Z, B] =
      Pure(r > s)

    override def foldMap[->>[_,_]](f: [x, y] => (x -> y) => (x ->> y))(using SymmetricSemigroupalCategory[->>, |*|]): A ->> B =
      s.fold

    override def inFst[Y]: Shuffled[A |*| Y, B |*| Y] =
      Pure(~⚬.fst(s))

    override def inSnd[X]: Shuffled[X |*| A, X |*| B] =
      Pure(~⚬.snd(s))

    override def unconsSome: UnconsSomeRes[A, B] =
      UnconsSomeRes.Pure(s)

    override def project[C](
      p: Projection[|*|, B, C],
      f: [X, Y, Z] => (X -> Y, Projection[|*|, Y, Z]) => ProjectRes[X, Z],
    ): ProjectRes[A, C] =
      s.project(p) match
        case ~⚬.ProjectRes.Projected(p0, s0) => ProjectRes.Projected(p0, Pure(s0))

    override def chaseBw[G[_], X](i: Focus[|*|, G])(using ev: B =:= G[X]): ChaseBwRes[A, G, X] =
      s.chaseBw(i) match
        case tr: ~⚬.ChaseBwRes.Transported[a, f, g, x] =>
          ChaseBwRes.Transported(tr.ev, Punched.pure(tr.s))
        case ~⚬.ChaseBwRes.Split(ev) =>
          ChaseBwRes.Split(ev)

    override def chaseFw[F[_], X](i: Focus[|*|, F])(using A =:= F[X]): ChaseFwRes[F, X, B] =
      s.chaseFw(i) match
        case tr: ~⚬.ChaseFwRes.Transported[f, x, g, b] =>
          ChaseFwRes.Transported(Punched.pure(tr.s), tr.ev)
        case ~⚬.ChaseFwRes.Split(ev) =>
          ChaseFwRes.Split(ev)

    override def translate[->>[_, _], <*>[_, _], F[_, _], S](
      fa: F[A, S],
      om: SemigroupalObjectMap[|*|, <*>, F],
      am: ArrowMap[->, ->>, F],
    )(using
      tgt: libretto.lambda.Shuffled[->>, <*>],
    ): Exists[[T] =>> (tgt.Shuffled[S, T], F[B, T])] =
      s.translate(fa)(om, tgt.shuffle) match
        case Exists.Some((s1, fb)) =>
          Exists((tgt.Pure(s1), fb))

    override def traverse[G[_], ->>[_,_]](
      f: [t, u] => (t -> u) => G[t ->> u],
    )(using
      tgt: libretto.lambda.Shuffled.With[->>, |*|, shuffle.type],
      G: Applicative[G],
    ): G[tgt.Shuffled[A, B]] =
      Applicative[G].pure(tgt.Pure(s))

    override def sweepL[F[_], ->>[_,_]](
      a: F[A],
      f: [t, u] => (F[t], t -> u) => (t ->> u, F[u]),
    )(using
      tgt: libretto.lambda.Shuffled.With[->>, |*|, shuffle.type],
      F: StrongZippable[|*|, F],
    ): (tgt.Shuffled[A, B], F[B]) =
      (tgt.Pure(s), s.apply(a))
  }

  case class SemiObstructed[A, X1, X2, Y2, Z2, B1, B2](
    left    : A ~⚬ (X1 |*| X2),
    bottom1 : Plated[X2, Y2],
    bottom2 : Y2 ~⚬ Z2,
    right   : TransferOpt[X1, Z2, B1, B2],
  ) extends Permeable[A, B1 |*| B2] {
    override def after[Z](that: Shuffled[Z, A]): Shuffled[Z, B1 |*| B2] =
      that match {
        case Pure(s) =>
          SemiObstructed(s > left, bottom1, bottom2, right)
        case Impermeable(l, m, r) =>
          ~⚬.decompose1((r > left).invert) match {
            case ~⚬.Decomposition1(f1, f2, g, ev) =>
              val m1 = Plated.SemiSnoc(ev.flip.substituteCo(m), RevTransferOpt(g), f2.invert, bottom1)
              Impermeable(l, m1, ~⚬.par(f1.invert, bottom2) > right.asShuffle)
          }
        case SemiObstructed(l, b1, b2, r) =>
          ▄░▄(b1, ~⚬.snd(b2) > r.asShuffle > left, bottom1)
            .afterShuffle(l)
            .thenShuffle(~⚬.snd(bottom2) > right.asShuffle)
      }

    override def thenShuffle[C](s: (B1 |*| B2) ~⚬ C): Permeable[A, C] =
      ~⚬.decompose1(right.asShuffle > s) match {
        case ~⚬.Decomposition1(g1, g2, h, ev) => ev.substituteCo[Permeable[A, _]](SemiObstructed(left > ~⚬.fst(g1), bottom1, bottom2 > g2, h))
      }

    override def afterShuffle[Z](that: Z ~⚬ A): Shuffled[Z, B1 |*| B2] =
      SemiObstructed(that > left, bottom1, bottom2, right)

    override def foldMap[->>[_,_]](tr: [x, y] => (x: x -> y) => ->>[x, y])(using
      ev: SymmetricSemigroupalCategory[->>, |*|],
    ): A ->> (B1 |*| B2) = {
      val (f, g, h, i) = (left.fold, bottom1.foldMap(tr), bottom2.fold, right.fold)
      ev.andThen(f, ev.andThen(ev.snd(ev.andThen(g, h)), i))
    }

    override def inFst[Q]: Shuffled[A |*| Q, (B1 |*| B2) |*| Q] =
      swap > inSnd[Q] > swap

    override def inSnd[P]: Shuffled[P |*| A, P |*| (B1 |*| B2)] =
      ~⚬.decompose[P |*| X1, Y2, P, B1 |*| B2](~⚬.snd(bottom2) > ~⚬.assocLR > ~⚬.snd(right.asShuffle)) match {
        case ~⚬.Decomposition(f1, f2, h) =>
          SemiObstructed(~⚬.snd(left) > ~⚬.assocRL > ~⚬.fst(f1), bottom1, f2, h)
      }

    override def project[C](
      p: Projection[|*|, B1 |*| B2, C],
      f: [P, Q, R] => (P -> Q, Projection[|*|, Q, R]) => ProjectRes[P, R],
    ): ProjectRes[A, C] =
      p match
        case Projection.Id()         => ProjectRes.Projected(P.id, this)
        case p: P.Proper[pr, b12, c] => this.projectProper(p, f)

    private def projectProper[C](
      p: Projection.Proper[|*|, B1 |*| B2, C],
      f: [P, Q, R] => (P -> Q, Projection[|*|, Q, R]) => ProjectRes[P, R],
    ): ProjectRes[A, C] =
      right.projectProper(p) match
        case res @ ~⚬.ProjectProperRes.Projected(p0, right1) =>
          p0.fromPair[X1, Z2].switch(
            caseDiscardFst = { p2 =>
              bottom2.project(p2) match
                case ~⚬.ProjectRes.Projected(q, bot2) =>
                  bottom1.project(q, f) match
                    case ProjectRes.Projected(q0, bot1) =>
                      left.projectProper(P.discardFst(q0)) match
                        case ~⚬.ProjectProperRes.Projected(r, left1) =>
                          ProjectRes.Projected(r, Pure(left1) > bot1 > Pure(bot2) > Pure(right1))
            },
            caseDiscardSnd = p1 =>
              UnhandledCase.raise(s"${SemiObstructed.this.getClass.getSimpleName}.projectProper caseDiscardSnd($p1)"),
            casePar = [Q1, Q2] => (ev: res.X =:= (Q1 |*| Q2)) ?=> (p12: P.Par[|*|, X1, Z2, Q1, Q2]) =>
              p12 match
                case P.Fst(p1) =>
                  summon[Z2 =:= Q2]
                  left.projectProper(p1.inFst[X2]) match
                    case ~⚬.ProjectProperRes.Projected(p0, left1) =>
                      ProjectRes.Projected(
                        p0,
                        Pure(left1) > snd(bottom1.asShuffled > Pure(bottom2)) > Pure(right1.from(using ev.flip)),
                      )
                case other =>
                  UnhandledCase.raise(s"${SemiObstructed.this.getClass.getSimpleName}.projectProper casePar $other"),
          )

    override def unconsSome: UnconsSomeRes[A, B1 |*| B2] =
      bottom1.unconsSome match
        case c: Plated.UnconsSomeRes.Cons[f, x, y, y2] =>
          UnconsSomeRes.Cons[A, [t] =>> X1 |*| f[t], x, y, B1 |*| B2](
            left,
            Focus.snd(c.i),
            c.f,
            (c.post thenShuffle bottom2).inSnd thenShuffle right.asShuffle,
          )

    override def translate[->>[_,_], <*>[_,_], F[_,_], S](
      fa: F[A, S],
      om: SemigroupalObjectMap[|*|, <*>, F],
      am: ArrowMap[->, ->>, F],
    )(using
      tgt: libretto.lambda.Shuffled[->>, <*>],
    ): Exists[[T] =>> (tgt.Shuffled[S, T], F[B1 |*| B2, T])] =
      UnhandledCase.raise(s"${this.getClass.getSimpleName}.translate")

    override def sweepL[F[_], ->>[_,_]](
      a: F[A],
      f: [t, u] => (F[t], t -> u) => (t ->> u, F[u]),
    )(using
      tgt: libretto.lambda.Shuffled.With[->>, |*|, shuffle.type],
      F: StrongZippable[|*|, F],
    ): (tgt.Shuffled[A, B1 |*| B2], F[B1 |*| B2]) =
      UnhandledCase.raise(s"${this.getClass.getSimpleName}.sweepL")

    override def traverse[G[_], ->>[_, _]](
      f: [t, u] => (t -> u) => G[->>[t, u]],
    )(using
      tgt: libretto.lambda.Shuffled.With[->>, |*|, shuffle.type],
      G: Applicative[G],
    ): G[tgt.Shuffled[A, B1 |*| B2]] =
      bottom1
        .traverse[G, ->>](f)
        .map(tgt.SemiObstructed(left, _, bottom2, right))

    override def chaseFw[F[_], T](i: Focus[|*|, F])(using A =:= F[T]): ChaseFwRes[F, T, B1 |*| B2] =
      ChaseFwRes(left.chaseFw(i))
        .thenSnd(bottom1.asShuffled > Pure(bottom2))
        .andThen(Pure(right.asShuffle))

    override def chaseBw[G[_], T](i: Focus[|*|, G])(using ev: (B1 |*| B2) =:= G[T]): ChaseBwRes[A, G, T] =
      UnhandledCase.raise(s"${this.getClass.getSimpleName}.chaseBw")
  }

  object Permeable {
    def id[X]: Permeable[X, X] =
      Pure(~⚬.Id())
  }

  sealed trait Plated[A, B] {
    import Plated.*

    infix def afterPermeable[Z](that: Permeable[Z, A]): Plated.Preshuffled[Z, ?, B] =
      that match {
        case Pure(s) =>
          Preshuffled(s, this)
        case SemiObstructed(l, b1, b2, r) =>
          Preshuffled(l, SemiCons(b1, b2, r, this))
      }

    infix def thenPermeable[C](that: Permeable[B, C]): Plated.Postshuffled[A, ?, C] =
      that match {
        case Pure(s) =>
          Postshuffled(this, s)
        case SemiObstructed(l, b1, b2, r) =>
          revDecompose1(l) match {
            case RevDecomposition1(ev, t, g1, g2) =>
              Postshuffled(SemiSnoc(this.to(using ev), t, g2, b1), ~⚬.par(g1, b2) > r.asShuffle)
          }
      }

    def impermeable: Impermeable[A, A, B, B] =
      Impermeable(~⚬.id, this, ~⚬.id)

    def asShuffled: Shuffled[A, B] =
      impermeable


    def foldMap[->>[_, _]](
      tr: [x, y] => (x -> y) => (x ->> y),
    )(using
      ev: SymmetricSemigroupalCategory[->>, |*|],
    ): A ->> B

    def fold(using ev: SymmetricSemigroupalCategory[->, |*|]): A -> B =
      foldMap([x, y] => (f: x -> y) => f)

    def unconsSome: Plated.UnconsSomeRes[A, B]

    def traverse[G[_], ->>[_,_]](
      f: [t, u] => (t -> u) => G[t ->> u],
    )(using
      tgt: libretto.lambda.Shuffled.With[->>, |*|, shuffle.type],
      G: Applicative[G],
    ): G[tgt.Plated[A, B]]

    def translate[->>[_, _], <*>[_, _], F[_, _], S](
      fa: F[A, S],
      om: SemigroupalObjectMap[|*|, <*>, F],
      am: ArrowMap[->, ->>, F],
    )(using
      tgt: libretto.lambda.Shuffled[->>, <*>],
    ): Exists[[T] =>> (tgt.Plated[S, T], F[B, T])]

    def sweepL[F[_], ->>[_,_]](
      a: F[A],
      f: [t, u] => (F[t], t -> u) => (t ->> u, F[u]),
    )(using
      tgt: libretto.lambda.Shuffled.With[->>, |*|, shuffle.type],
      F: StrongZippable[|*|, F],
    ): (tgt.Plated[A, B], F[B])

    def projectProper[C](
      p: Projection.Proper[|*|, B, C],
      f: [X, Y, Z] => (X -> Y, Projection[|*|, Y, Z]) => ProjectRes[X, Z],
    ): ProjectRes[A, C]

    def project[C](
      p: Projection[|*|, B, C],
      f: [X, Y, Z] => (X -> Y, Projection[|*|, Y, Z]) => ProjectRes[X, Z],
    ): ProjectRes[A, C] =
      p match {
        case Projection.Id()                 => ProjectRes.Projected(Projection.Id(), this.asShuffled)
        case p: Projection.Proper[|*|, B, C] => projectProper(p, f)
      }

    def chaseFw[F[_], X](i: Focus[|*|, F])(using A =:= F[X]): ChaseFwRes[F, X, B]
    def chaseBw[G[_], X](i: Focus[|*|, G])(using B =:= G[X]): ChaseBwRes[A, G, X]

    def to[C](using ev: B =:= C): Plated[A, C] =
      ev.substituteCo(this)
  }

  object Plated {
    sealed trait BiInput[A1, A2, B] extends Plated[A1 |*| A2, B] {
      def chaseFwFst[F[_], X](i: Focus[|*|, F])(using ev: A1 =:= F[X]): ChaseFwRes[[x] =>> F[x] |*| A2, X, B]
      def chaseFwSnd[F[_], X](i: Focus[|*|, F])(using ev: A2 =:= F[X]): ChaseFwRes[[x] =>> A1 |*| F[x], X, B]

      final override def chaseFw[F[_], X](i: Focus[|*|, F])(using ev: (A1 |*| A2) =:= F[X]): ChaseFwRes[F, X, B] =
        ev match { case TypeEq(Refl()) =>
          i match {
            case Focus.Id() =>
              ChaseFwRes.Split(ev.flip)
            case i: Focus.Fst[pair, f1, z] =>
              (ev andThen summon[F[X] =:= (f1[X] |*| z)]) match
                case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                  chaseFwFst[f1, X](i.i)
            case i: Focus.Snd[pair, f2, z] =>
              (ev andThen summon[F[X] =:= (z |*| f2[X])]) match
                case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                  chaseFwSnd[f2, X](i.i)
          }
        }
    }

    sealed trait BiOutput[A, B1, B2] extends Plated[A, B1 |*| B2] {
      def chaseBwFst[G[_], X](i: Focus[|*|, G])(using B1 =:= G[X]): ChaseBwRes[A, [x] =>> G[x] |*| B2, X]
      def chaseBwSnd[G[_], X](i: Focus[|*|, G])(using B2 =:= G[X]): ChaseBwRes[A, [x] =>> B1 |*| G[x], X]

      final override def chaseBw[G[_], X](i: Focus[|*|, G])(using ev: (B1 |*| B2) =:= G[X]): ChaseBwRes[A, G, X] =
        i match
          case Focus.Id() =>
            ChaseBwRes.Split(ev.flip)
          case j: Focus.Fst[p, g1, b2] =>
            (ev andThen summon[G[X] =:= (g1[X] |*| b2)]) match
              case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                chaseBwFst[g1, X](j.i)
          case j: Focus.Snd[pair, g2, b1] =>
            (ev andThen summon[G[X] =:= (b1 |*| g2[X])]) match
              case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                chaseBwSnd[g2, X](j.i)

      def discardFst(f: [X, Y, Z] => (X -> Y, Projection[|*|, Y, Z]) => ProjectRes[X, Z]): ProjectRes[A, B2]
      def discardSnd(f: [X, Y, Z] => (X -> Y, Projection[|*|, Y, Z]) => ProjectRes[X, Z]): ProjectRes[A, B1]

      def projectFst[C](
        p: Projection.Proper[|*|, B1, C],
        f: [X, Y, Z] => (X -> Y, Projection[|*|, Y, Z]) => ProjectRes[X, Z],
      ): ProjectRes[A, C |*| B2]

      def projectSnd[C](
        p: P.Proper[|*|, B2, C],
        f: [X, Y, Z] => (X -> Y, Projection[|*|, Y, Z]) => ProjectRes[X, Z],
      ): ProjectRes[A, B1 |*| C]

      final override def projectProper[C](
        p: P.Proper[|*|, B1 |*| B2, C],
        f: [X, Y, Z] => (X -> Y, Projection[|*|, Y, Z]) => ProjectRes[X, Z],
      ): ProjectRes[A, C] =
        p.fromPair[B1, B2].switch(
          caseDiscardFst = { p2 =>
            discardFst(f) match
              case ProjectRes.Projected(q0, s0) =>
                s0.project(p2, f) match
                  case ProjectRes.Projected(q1, s1) => ProjectRes.Projected(q0 > q1, s1)
          },
          caseDiscardSnd = { p1 =>
            discardSnd(f) match
              case ProjectRes.Projected(q0, s0) =>
                s0.project(p1, f) match
                  case ProjectRes.Projected(q1, s1) => ProjectRes.Projected(q0 > q1, s1)
          },
          casePar = [q1, q2] => (ev: C =:= (q1 |*| q2)) ?=> (p: P.Par[|*|, B1, B2, q1, q2]) =>                        ev match { case TypeEq(Refl()) =>
            p match
              case P.Fst(p1)      => projectFst(p1, f).to[C]
              case P.Snd(p2)      => projectSnd(p2, f).to[C]
              case P.Both(p1, p2) => projectFst(p1, f).project(P.snd(p2), f)
          },
        )
    }

    case class Solid[A, B](f: A -> B) extends Plated[A, B] {
      override def foldMap[->>[_,_]](tr: [x, y] => (x -> y) => ->>[x, y])(using
        ev: SymmetricSemigroupalCategory[->>, |*|],
      ): A ->> B =
        tr(f)

      override def unconsSome: UnconsSomeRes[A, B] =
        UnconsSomeRes.Cons(Focus.id, f, id)

      override def projectProper[C](
        p: Projection.Proper[|*|, B, C],
        h: [X, Y, Z] => (X -> Y, Projection[|*|, Y, Z]) => ProjectRes[X, Z],
      ): ProjectRes[A, C] =
        h(f, p)

      override def chaseFw[F[_], X](i: Focus[|*|, F])(using ev: A =:= F[X]): ChaseFwRes.Blocked[F, X, B] =
        ChaseFwRes.FedTo[F, X, F, B, [x] =>> x, B](Punched.id(i), i, ev.substituteCo[[x] =>> x -> B](f), Focus.id, id[B])

      override def chaseBw[G[_], X](i: Focus[|*|, G])(using ev: B =:= G[X]): ChaseBwRes.Blocked[A, G, X] =
        ChaseBwRes.OriginatesFrom[A, [x] =>> x, A, G, X, G](id[A], Focus.id, ev.substituteCo(f), i, Punched.id(i))

      override def traverse[G[_], ->>[_, _]](
        g: [t, u] => (t -> u) => G[t ->> u],
      )(using
        tgt: libretto.lambda.Shuffled.With[->>, |*|, shuffle.type],
        G: Applicative[G],
      ): G[tgt.Plated[A, B]] =
        g(f).map(tgt.Plated.Solid(_))

      override def translate[->>[_, _], <*>[_, _], F[_, _], S](
        fa: F[A, S],
        om: SemigroupalObjectMap[|*|, <*>, F],
        am: ArrowMap[->, ->>, F],
      )(using
        tgt: libretto.lambda.Shuffled[->>, <*>],
      ): Exists[[T] =>> (tgt.Plated[S, T], F[B, T])] = {
        am.map(fa, f)(using om) match
          case Exists.Some((g, fb)) =>
            Exists((tgt.Plated.Solid(g), fb))
      }

      override def sweepL[F[_], ->>[_, _]](
        a: F[A],
        g: [t, u] => (F[t], t -> u) => (t ->> u, F[u]),
      )(using
        tgt: libretto.lambda.Shuffled.With[->>, |*|, shuffle.type],
        F: StrongZippable[|*|, F],
      ): (tgt.Plated[A, B], F[B]) = {
        val (f1, b) = g(a, f)
        (tgt.Plated.Solid(f1), b)
      }
    }

    case class Stacked[A1, A2, B1, B2](
      f1: Plated[A1, B1],
      f2: Plated[A2, B2],
    ) extends BiInput[A1, A2, B1 |*| B2] with BiOutput[A1 |*| A2, B1, B2] {
      override def foldMap[->>[_,_]](tr: [x, y] => (x -> y) => ->>[x, y])(using
        ev: SymmetricSemigroupalCategory[->>, |*|],
      ): (A1 |*| A2) ->> (B1 |*| B2) =
        ev.par(f1.foldMap(tr), f2.foldMap(tr))

      override def unconsSome: UnconsSomeRes[A1 |*| A2, B1 |*| B2] =
        f1.unconsSome match
          case c: UnconsSomeRes.Cons[f, x, y, b1] =>
            UnconsSomeRes.Cons[[t] =>> f[t] |*| A2, x, y, B1 |*| B2](c.i.inFst[A2], c.f, par(c.post, f2.asShuffled))

      override def discardFst(f: [X, Y, Z] => (X -> Y, P[|*|, Y, Z]) => ProjectRes[X, Z]): ProjectRes[A1 |*| A2, B2] =
        ProjectRes.Projected(P.discardFst, f2.asShuffled)

      override def discardSnd(f: [X, Y, Z] => (X -> Y, P[|*|, Y, Z]) => ProjectRes[X, Z]): ProjectRes[A1 |*| A2, B1] =
        ProjectRes.Projected(P.discardSnd, f1.asShuffled)

      override def projectFst[C](p: Proper[|*|, B1, C], f: [X, Y, Z] => (X -> Y, P[|*|, Y, Z]) => ProjectRes[X, Z]): ProjectRes[A1 |*| A2, C |*| B2] =
        f1.project(p, f).inFst(f2.asShuffled)

      override def projectSnd[C](p: Proper[|*|, B2, C], f: [X, Y, Z] => (X -> Y, P[|*|, Y, Z]) => ProjectRes[X, Z]): ProjectRes[A1 |*| A2, B1 |*| C] =
        f2.project(p, f).inSnd(f1.asShuffled)

      override def chaseFwFst[F[_], X](i: Focus[|*|, F])(using ev: A1 =:= F[X]): ChaseFwRes[[x] =>> F[x] |*| A2, X, B1 |*| B2] =
        f1.chaseFw[F, X](i).inFst(snd = f2.asShuffled)

      override def chaseFwSnd[F[_], X](i: Focus[|*|, F])(using ev: A2 =:= F[X]): ChaseFwRes[[x] =>> A1 |*| F[x], X, B1 |*| B2] =
        f2.chaseFw[F, X](i).inSnd(fst = f1.asShuffled)

      override def chaseBwFst[G[_], X](i: Focus[|*|, G])(using B1 =:= G[X]): ChaseBwRes[A1 |*| A2, [x] =>> G[x] |*| B2, X] =
        f1.chaseBw[G, X](i).inFst(snd = f2.asShuffled)

      override def chaseBwSnd[G[_], X](i: Focus[|*|, G])(using B2 =:= G[X]): ChaseBwRes[A1 |*| A2, [x] =>> B1 |*| G[x], X] =
        f2.chaseBw[G, X](i).inSnd(fst = f1.asShuffled)

      override def traverse[G[_], ->>[_, _]](
        f: [t, u] => (t -> u) => G[t ->> u],
      )(using
        tgt: libretto.lambda.Shuffled.With[->>, |*|, shuffle.type],
        G: Applicative[G],
      ): G[tgt.Plated[A1 |*| A2, B1 |*| B2]] =
        Applicative[G].map2(
          f1.traverse(f),
          f2.traverse(f),
        ) { (g1, g2) =>
          tgt.Plated.Stacked(g1, g2)
        }

      override def sweepL[F[_], ->>[_, _]](
        a: F[A1 |*| A2],
        f: [t, u] => (F[t], t -> u) => (t ->> u, F[u]),
      )(using
        tgt: libretto.lambda.Shuffled.With[->>, |*|, shuffle.type],
        F: StrongZippable[|*|, F],
      ): (tgt.Plated[A1 |*| A2, B1 |*| B2], F[B1 |*| B2]) = {
        val F.Unzip(a1, a2) = a
        val (g1, b1) = f1.sweepL[F, ->>](a1, f)
        val (g2, b2) = f2.sweepL[F, ->>](a2, f)
        (tgt.Plated.Stacked(g1, g2), F.zip(b1, b2))
      }

      override def translate[->>[_, _], <*>[_, _], F[_, _], S](
        fa12: F[A1 |*| A2, S],
        om: SemigroupalObjectMap[|*|, <*>, F],
        am: ArrowMap[->, ->>, F],
      )(using
        tgt: libretto.lambda.Shuffled[->>, <*>],
      ): Exists[[T] =>> (tgt.Plated[S, T], F[B1 |*| B2, T])] = {
        om.unpair(fa12) match
          case om.Unpaired.Impl(fa1, fa2) =>
            f1.translate(fa1, om, am) match
              case Exists.Some((g1, fb1)) =>
                f2.translate(fa2, om, am) match
                  case Exists.Some((g2, fb2)) =>
                    Exists((tgt.Plated.Stacked(g1, g2), om.pair(fb1, fb2)))
      }
    }

    case class Sandwich[A, X, Y, B](l: Plated[A, X], m: X ~⚬ Y, r: Plated[Y, B]) extends Plated[A, B] {
      override def foldMap[->>[_,_]](tr: [x, y] => (x -> y) => (x ->> y))(using
        ev: SymmetricSemigroupalCategory[->>, |*|],
      ): A ->> B =
        ev.andThen(l.foldMap(tr), ev.andThen(m.fold, r.foldMap(tr)))

      override def unconsSome: UnconsSomeRes[A, B] =
        l.unconsSome match
          case c: UnconsSomeRes.Cons[f, v, w, x] =>
            UnconsSomeRes.Cons(c.i, c.f, (c.post thenShuffle m) > r.asShuffled)

      override def projectProper[C](
        p: Projection.Proper[|*|, B, C],
        f: [P, Q, R] => (P -> Q, Projection[|*|, Q, R]) => ProjectRes[P, R],
      ): ProjectRes[A, C] =
        r.projectProper(p, f).after(l.asShuffled thenShuffle m, f)

      override def chaseFw[F[_], X](i: Focus[|*|, F])(using A =:= F[X]): ChaseFwRes[F, X, B] =
        l.chaseFw(i) andThen (Pure(m) > r.asShuffled)

      override def chaseBw[G[_], X](i: Focus[|*|, G])(using ev: B =:= G[X]): ChaseBwRes[A, G, X] =
        r.chaseBw(i) after (l.asShuffled thenShuffle m)

      override def traverse[G[_], ->>[_, _]](
        f: [t, u] => (t -> u) => G[t ->> u],
      )(using
        tgt: libretto.lambda.Shuffled.With[->>, |*|, shuffle.type],
        G: Applicative[G],
      ): G[tgt.Plated[A, B]] = {
        Applicative[G].map2(
          l.traverse(f),
          r.traverse(f),
        ) { (l1, r1) =>
          tgt.Plated.Sandwich(l1, m, r1)
        }
      }

      override def sweepL[F[_], ->>[_, _]](
        a: F[A],
        f: [t, u] => (F[t], t -> u) => (t ->> u, F[u]),
      )(using
        tgt: libretto.lambda.Shuffled.With[->>, |*|, shuffle.type],
        F: StrongZippable[|*|, F],
      ): (tgt.Plated[A, B], F[B]) = {
        val (l1, x) = l.sweepL[F, ->>](a, f)
        val y = m(x)
        val (r1, b) = r.sweepL[F, ->>](y, f)
        (tgt.Plated.Sandwich(l1, m, r1), b)
      }

      override def translate[->>[_, _], <*>[_, _], F[_, _], S](
        fa: F[A, S],
        om: SemigroupalObjectMap[|*|, <*>, F],
        am: ArrowMap[->, ->>, F],
      )(using
        tgt: libretto.lambda.Shuffled[->>, <*>],
      ): Exists[[T] =>> (tgt.Plated[S, T], F[B, T])] = {
        l.translate(fa, om, am) match
          case Exists.Some((l1, fx)) =>
            m.translate(fx)(om, tgt.shuffle) match
              case Exists.Some((m1, fy)) =>
                r.translate(fy, om, am) match
                  case Exists.Some((r1, fb)) =>
                    Exists(tgt.Plated.Sandwich(l1, m1, r1), fb)
      }
    }

    case class SemiCons[A1, A2, X2, Y2, Z1, Z2, B](
      semiHead: Plated[A2, X2],
      s: X2 ~⚬ Y2,
      t: TransferOpt[A1, Y2, Z1, Z2],
      tail: Plated[Z1 |*| Z2, B],
    ) extends BiInput[A1, A2, B] {
      override def foldMap[->>[_,_]](tr: [x, y] => (x -> y) => (x ->> y))(using
        ev: SymmetricSemigroupalCategory[->>, |*|],
      ): (A1 |*| A2) ->> B =
        ev.andThen(ev.andThen(ev.snd(ev.andThen(semiHead.foldMap(tr), s.fold)), t.fold), tail.foldMap(tr))

      override def unconsSome: UnconsSomeRes[A1 |*| A2, B] =
        semiHead.unconsSome match
          case c: UnconsSomeRes.Cons[f, v, w, x2] =>
            UnconsSomeRes.Cons[[t] =>> A1 |*| f[t], v, w, B](
              c.i.inSnd,
              c.f,
              ((c.post thenShuffle s).inSnd thenShuffle t.asShuffle) > tail.asShuffled,
            )

      override def projectProper[C](
        p: Projection.Proper[|*|, B, C],
        f: [P, Q, R] => (P -> Q, Projection[|*|, Q, R]) => ProjectRes[P, R],
      ): ProjectRes[A1 |*| A2, C] =
        tail.projectProper(p, f) match
          case ProjectRes.Projected(p0, h) =>
            SemiObstructed(~⚬.id[A1 |*| A2], semiHead, s, t).project(p0, f) match
              case ProjectRes.Projected(q, g) =>
                ProjectRes.Projected(q, g > h)

      override def chaseFwFst[F[_], X](i: Focus[|*|, F])(using ev: A1 =:= F[X]): ChaseFwRes[[x] =>> F[x] |*| A2, X, B] =
        ev match { case TypeEq(Refl()) =>
          Impermeable(t.asShuffle, tail, ~⚬.id[B])
            .chaseFw[[x] =>> F[x] |*| Y2, X](i.inFst)
            .after(i.inFst[A2], [x] => (_: Unit) => (semiHead.asShuffled > Pure(s)).inSnd[F[x]])
        }

      override def chaseFwSnd[F[_], X](i: Focus[|*|, F])(using ev: A2 =:= F[X]): ChaseFwRes[[x] =>> A1 |*| F[x], X, B] =
        semiHead.chaseFw[F, X](i)
          .andThen(Pure(s))
          .inSnd[A1]
          .andThen(Pure(t.asShuffle) > tail.asShuffled)

      override def chaseBw[G[_], T](i: Focus[|*|, G])(using ev: B =:= G[T]): ChaseBwRes[A1 |*| A2, G, T] =
        tail.chaseBw(i) after (semiHead.asShuffled thenShuffle s).inSnd[A1].thenShuffle(t.asShuffle)

      override def traverse[G[_], ->>[_, _]](
        f: [t, u] => (t -> u) => G[t ->> u],
      )(using
        tgt: libretto.lambda.Shuffled.With[->>, |*|, shuffle.type],
        G: Applicative[G],
      ): G[tgt.Plated[A1 |*| A2, B]] =
        Applicative[G].map2(
          semiHead.traverse(f),
          tail.traverse(f),
        ) { (semiHead1, tail1) =>
          tgt.Plated.SemiCons(semiHead1, s, t, tail1)
        }

      override def sweepL[F[_], ->>[_, _]](
        a: F[A1 |*| A2],
        f: [t, u] => (F[t], t -> u) => (t ->> u, F[u]),
      )(using
        tgt: libretto.lambda.Shuffled.With[->>, |*|, shuffle.type],
        F: StrongZippable[|*|, F],
      ): (tgt.Plated[A1 |*| A2, B], F[B]) = {
        val F.Unzip(a1, a2) = a
        val (semiHead1, x2) = semiHead.sweepL[F, ->>](a2, f)
        val y2              = s.apply(x2)
        val z12             = t.apply(F.zip(a1, y2))
        val (tail1, b)      = tail.sweepL[F, ->>](z12, f)
        (tgt.Plated.SemiCons(semiHead1, s, t, tail1), b)
      }

      override def translate[->>[_, _], <*>[_, _], F[_, _], S](
        fa: F[A1 |*| A2, S],
        om: SemigroupalObjectMap[|*|, <*>, F],
        am: ArrowMap[->, ->>, F],
      )(using
        tgt: libretto.lambda.Shuffled[->>, <*>],
      ): Exists[[T] =>> (tgt.Plated[S, T], F[B, T])] =
        om.unpair(fa) match
          case om.Unpaired.Impl(fa1, fa2) =>
            semiHead.translate(fa2, om, am) match
              case Exists.Some((semiHead1, fx2)) =>
                s.translate(fx2)(om, tgt.shuffle) match
                  case Exists.Some((s1, fy2)) =>
                    t.translateLR(fa1, fy2)(om)(using tgt.shuffle) match
                      case Exists.Some(Exists.Some((t1, fz1, fz2))) =>
                        tail.translate(om.pair(fz1, fz2), om, am) match
                          case Exists.Some((tail1, fb)) =>
                            Exists((tgt.Plated.SemiCons(semiHead1, s1, t1, tail1), fb))
    }

    case class SemiSnoc[A, X1, X2, Y2, Z2, B1, B2](
      init: Plated[A, X1 |*| X2],
      t: RevTransferOpt[X1, X2, B1, Y2],
      s: Y2 ~⚬ Z2,
      semiLast: Plated[Z2, B2],
    ) extends BiOutput[A, B1, B2] {
      override def foldMap[->>[_,_]](tr: [x, y] => (x -> y) => (x ->> y))(using
        ev: SymmetricSemigroupalCategory[->>, |*|],
      ): A ->> (B1 |*| B2) =
        ev.andThen(init.foldMap(tr), ev.andThen(t.fold, ev.snd(ev.andThen(s.fold, semiLast.foldMap(tr)))))

      override def unconsSome: UnconsSomeRes[A, B1 |*| B2] =
        init.unconsSome match
          case c: UnconsSomeRes.Cons[f, v, w, x1x2] =>
            UnconsSomeRes.Cons(c.i, c.f, (c.post thenShuffle t.asShuffle) > (Pure(s) > semiLast.asShuffled).inSnd)

      override def discardFst(f: [X, Y, Z] => (X -> Y, Projection[|*|, Y, Z]) => ProjectRes[X, Z]): ProjectRes[A, B2] =
        t.asShuffle.projectProper(P.discardFst) match
          case ~⚬.ProjectProperRes.Projected(p, t1) =>
            init.projectProper(p, f) match
              case ProjectRes.Projected(p0, init1) =>
                ProjectRes.Projected(p0, init1 > Pure(t1) > Pure(s) > semiLast.asShuffled)

      override def discardSnd(f: [X, Y, Z] => (X -> Y, Projection[|*|, Y, Z]) => ProjectRes[X, Z]): ProjectRes[A, B1] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.discardSnd")

      override def projectFst[C](p1: Proper[|*|, B1, C], f: [X, Y, Z] => (X -> Y, Projection[|*|, Y, Z]) => ProjectRes[X, Z]): ProjectRes[A, C |*| B2] =
        ProjectRes(t.asShuffle.projectProper(p1.inFst[Y2]))
          .after(init.asShuffled, f)
          .andThen(snd(Pure(s) > semiLast.asShuffled))

      override def projectSnd[C](p2: Proper[|*|, B2, C], f: [X, Y, Z] => (X -> Y, Projection[|*|, Y, Z]) => ProjectRes[X, Z]): ProjectRes[A, B1 |*| C] =
        semiLast.project(p2, f)
          .after(Pure(s), f)
          .inSnd[B1]
          .after(init.asShuffled thenShuffle t.asShuffle, f)

      override def chaseFw[F[_], T](i: Focus[|*|, F])(using A =:= F[T]): ChaseFwRes[F, T, B1 |*| B2] =
        init.chaseFw[F, T](i)
          .andThen(Pure(t.asShuffle > ~⚬.snd(s)) > snd(semiLast.asShuffled))

      override def chaseBwFst[G[_], T](i: Focus[|*|, G])(using ev: B1 =:= G[T]): ChaseBwRes[A, [x] =>> G[x] |*| B2, T] =
        ev match {
          case TypeEq(Refl()) =>
            ChaseBwRes(t.asShuffle.chaseBw[[t] =>> G[t] |*| Y2, T](i.inFst))
              .after(init.asShuffled)
              .andThen(
                i.inFst[B2],
                [t] => (_: Unit) => (Pure(s) > semiLast.asShuffled).inSnd[G[t]],
              )
        }

      override def chaseBwSnd[G[_], T](i: Focus[|*|, G])(using B2 =:= G[T]): ChaseBwRes[A, [x] =>> B1 |*| G[x], T] =
        semiLast.chaseBw[G, T](i)
          .after(Pure(s))
          .inSnd[B1]
          .after(init.asShuffled > Pure(t.asShuffle))

      override def traverse[G[_], ->>[_, _]](
        f: [t, u] => (t -> u) => G[t ->> u],
      )(using
        tgt: libretto.lambda.Shuffled.With[->>, |*|, shuffle.type],
        G: Applicative[G],
      ): G[tgt.Plated[A, B1 |*| B2]] =
        Applicative[G].map2(
          init.traverse(f),
          semiLast.traverse(f),
        ) { (init1, semiLast1) =>
          tgt.Plated.SemiSnoc(init1, t.rebase(tgt), s, semiLast1)
        }

      override def sweepL[F[_], ->>[_, _]](
        a: F[A],
        f: [t, u] => (F[t], t -> u) => (t ->> u, F[u]),
      )(using
        tgt: libretto.lambda.Shuffled.With[->>, |*|, shuffle.type],
        F: StrongZippable[|*|, F],
      ): (tgt.Plated[A, B1 |*| B2], F[B1 |*| B2]) = {
        val (init1, x) = init.sweepL[F, ->>](a, f)
        val (b1, y2)   = F.unzip(t.asShuffle(x))
        val z2         = s(y2)
        val (sl1, b2)  = semiLast.sweepL[F, ->>](z2, f)
        (tgt.Plated.SemiSnoc(init1, t.rebase(tgt), s, sl1), F.zip(b1, b2))
      }

      override def translate[->>[_, _], <*>[_, _], F[_, _], S](
        fa: F[A, S],
        om: SemigroupalObjectMap[|*|, <*>, F],
        am: ArrowMap[->, ->>, F],
      )(using
        tgt: libretto.lambda.Shuffled[->>, <*>],
      ): Exists[[T] =>> (tgt.Plated[S, T], F[B1 |*| B2, T])] = {
        init.translate(fa, om, am) match
          case Exists.Some((init1, fx)) =>
            val ufx = om.unpair(fx)
            t.translate(ufx.f1, ufx.f2, om) match
              case Exists.Some(Exists.Some((t1, fb1, fy2))) =>
                s.translate(fy2)(om, tgt.shuffle) match
                  case Exists.Some((s1, fz2)) =>
                    semiLast.translate(fz2, om, am) match
                      case Exists.Some((semiLast1, fb2)) =>
                        ufx.ev match
                          case TypeEq(Refl()) =>
                            Exists((tgt.Plated.SemiSnoc(init1.to(using ufx.ev), t1, s1, semiLast1), om.pair(fb1, fb2)))
      }
    }

    case class XI[A1, A2, P1, P2, Q, R, S1, S2, B1, B2](
      l: Plated[A2, P1 |*| P2],
      lt: RevTransferOpt[P1, P2, B1, Q],
      b: Q ~⚬ R,
      rt: TransferOpt[A1, R, S1, S2],
      r: Plated[S1 |*| S2, B2],
    ) extends BiInput[A1, A2, B1 |*| B2] with BiOutput[A1 |*| A2, B1, B2] {
      override def foldMap[->>[_,_]](tr: [x, y] => (x -> y) => (x ->> y))(using
        ev: SymmetricSemigroupalCategory[->>, |*|],
      ): (A1 |*| A2) ->> (B1 |*| B2) = {
        import ev.andThen
        andThen(
          ev.snd(andThen(l.foldMap(tr), andThen(lt.fold, ev.snd(b.fold)))),
          andThen(
            ev.xi,
            ev.snd(andThen(rt.fold, r.foldMap(tr))),
          ),
        )
      }

      override def unconsSome: UnconsSomeRes[A1 |*| A2, B1 |*| B2] =
        l.unconsSome match
          case c: UnconsSomeRes.Cons[f, x, y, p1p2] =>
            UnconsSomeRes.Cons[[t] =>> A1 |*| f[t], x, y, B1 |*| B2](
              c.i.inSnd,
              c.f,
              ((c.post thenShuffle (lt.asShuffle > ~⚬.snd(b))).inSnd[A1] thenShuffle ~⚬.xi) > (Pure(rt.asShuffle) > r.asShuffled).inSnd,
            )

      override def discardFst(f: [X, Y, Z] => (X -> Y, P[|*|, Y, Z]) => ProjectRes[X, Z]): ProjectRes[A1 |*| A2, B2] =
        lt.project(P.discardFst)
          .after(l.asShuffled, f)
          .andThen(Pure(b))
          .inSnd[A1]
          .andThen(Pure(rt.asShuffle))
          .andThen(r.asShuffled)

      override def discardSnd(f: [X, Y, Z] => (X -> Y, P[|*|, Y, Z]) => ProjectRes[X, Z]): ProjectRes[A1 |*| A2, B1] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.discardSnd")

      override def projectFst[C](p: Proper[|*|, B1, C], f: [X, Y, Z] => (X -> Y, P[|*|, Y, Z]) => ProjectRes[X, Z]): ProjectRes[A1 |*| A2, C |*| B2] =
        lt.project(p.inFst[Q])
          .after(l.asShuffled, f)
          .andThen(Pure(b).inSnd)
          .inSnd[A1]
          .andThen(xi > snd(Pure(rt.asShuffle) > r.asShuffled))

      override def projectSnd[C](p: Proper[|*|, B2, C], f: [X, Y, Z] => (X -> Y, P[|*|, Y, Z]) => ProjectRes[X, Z]): ProjectRes[A1 |*| A2, B1 |*| C] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.projectSnd")

      override def chaseFwFst[F[_], X](i: Focus[|*|, F])(using ev: A1 =:= F[X]): ChaseFwRes[[x] =>> F[x] |*| A2, X, B1 |*| B2] =
        ev match { case TypeEq(Refl()) =>
          Impermeable(rt.asShuffle, r, ~⚬.id)
            .chaseFw[[t] =>> F[t] |*| R, X](i.inFst[R])
            .inSnd[B1]
            .after(
              i.inFst[A2],
              [x] => (_: Unit) => (l.asShuffled > Pure(lt.asShuffle) > Pure(b).inSnd[B1]).inSnd[F[x]] > xi,
            )
        }

      override def chaseFwSnd[F[_], X](i: Focus[|*|, F])(using ev: A2 =:= F[X]): ChaseFwRes[[x] =>> A1 |*| F[x], X, B1 |*| B2] =
        l.chaseFw[F, X](i)
          .andThen(Pure(lt.asShuffle > ~⚬.snd(b)))
          .inSnd[A1]
          .andThen(xi > snd(Pure(rt.asShuffle) > r.asShuffled))

      override def chaseBwFst[G[_], X](i: Focus[|*|, G])(using ev: B1 =:= G[X]): ChaseBwRes[A1 |*| A2, [x] =>> G[x] |*| B2, X] =
        (l.impermeable > Pure(lt.asShuffle > ~⚬.fst(~⚬.id[B1].to[G[X]])))
          .chaseBw(i.inFst[Q])
          .inSnd[A1]
          .andThen[[x] =>> G[x] |*| B2](
            i.inFst[B2],
            [x] => (_: Unit) => xi > snd(Pure(~⚬.snd(b) > rt.asShuffle) > r.asShuffled),
          )

      override def chaseBwSnd[G[_], X](i: Focus[|*|, G])(using B2 =:= G[X]): ChaseBwRes[A1 |*| A2, [x] =>> B1 |*| G[x], X] =
        r.chaseBw(i)
          .after(Pure(rt.asShuffle))
          .after(Pure(b).inSnd[A1])
          .inSnd[B1]
          .after(xi)
          .after((l.asShuffled > Pure(lt.asShuffle)).inSnd[A1])

      override def traverse[G[_], ->>[_, _]](
        f: [t, u] => (t -> u) => G[t ->> u],
      )(using
        tgt: libretto.lambda.Shuffled.With[->>, |*|, shuffle.type],
        G: Applicative[G],
      ): G[tgt.Plated[A1 |*| A2, B1 |*| B2]] =
        Applicative[G].map2(
          l.traverse(f),
          r.traverse(f),
        ) { (l1, r1) =>
          tgt.Plated.XI(l1, lt.rebase(tgt), b, rt, r1)
        }

      override def sweepL[F[_], ->>[_, _]](
        fa: F[A1 |*| A2],
        f: [t, u] => (F[t], t -> u) => (t ->> u, F[u]),
      )(using
        tgt: libretto.lambda.Shuffled.With[->>, |*|, shuffle.type],
        F: StrongZippable[|*|, F],
      ): (tgt.Plated[A1 |*| A2, B1 |*| B2], F[B1 |*| B2]) = {
        val (fa1, fa2)       = F.unzip(fa)
        val (l1, fp12)       = l.sweepL[F, ->>](fa2, f)
        val F.Unzip(fb1, fq) = lt.apply(fp12)
        val fr               = b.apply(fq)
        val fs12             = rt.apply(F.zip(fa1, fr))
        val (r1, fb2)        = r.sweepL[F, ->>](fs12, f)
        (
          tgt.Plated.XI(l1, lt.rebase(tgt), b, rt, r1),
          F.zip(fb1, fb2),
        )
      }

      override def translate[->>[_, _], <*>[_, _], F[_, _], S](
        fa: F[A1 |*| A2, S],
        om: SemigroupalObjectMap[|*|, <*>, F],
        am: ArrowMap[->, ->>, F],
      )(using
        tgt: libretto.lambda.Shuffled[->>, <*>],
      ): Exists[[T] =>> (tgt.Plated[S, T], F[B1 |*| B2, T])] = {
        om.unpair(fa) match
          case om.Unpaired.Impl(fa1, fa2) =>
            l.translate(fa2, om, am) match
              case Exists.Some((l1, fp)) =>
                om.unpair(fp) match
                  case v @ om.Unpaired.Impl(fp1, fp2) =>
                    lt.translate(fp1, fp2, om) match
                      case Exists.Some(Exists.Some((lt1, fb1, fq))) =>
                        b.translate(fq)(om, tgt.shuffle) match
                          case Exists.Some((b1, fr)) =>
                            rt.translateLR(fa1, fr)(om)(using tgt.shuffle) match
                              case Exists.Some(Exists.Some((rt1, fs1, fs2))) =>
                                r.translate(om.pair(fs1, fs2), om, am) match
                                  case Exists.Some((r1, fb2)) =>
                                    Exists((tgt.Plated.XI(l1.to(using v.ev), lt1, b1, rt1, r1), om.pair(fb1, fb2)))
      }
    }

    case class Preshuffled[A, X, B](s: A ~⚬ X, t: Plated[X, B])
    case class Postshuffled[A, X, B](f: Plated[A, X], s: X ~⚬ B)

    enum UnconsSomeRes[A, B] {
      case Cons[F[_], X, Y, B](
        i: Focus[|*|, F],
        f: X -> Y,
        post: Shuffled[F[Y], B],
      ) extends UnconsSomeRes[F[X], B]
    }
  }
  import Plated.*

  case class RevTransferOpt[A1, A2, B1, B2](t: TransferOpt[B1, B2, A1, A2]) {
    def fold[->>[_, _]](using ev: SymmetricSemigroupalCategory[->>, |*|]): (A1 |*| A2) ->> (B1 |*| B2) =
      this.asShuffle.fold

    def asShuffle: (A1 |*| A2) ~⚬ (B1 |*| B2) =
      t.asShuffle.invert

    def rebase[->>[_, _]](tgt: libretto.lambda.Shuffled.With[->>, |*|, shuffle.type]): tgt.RevTransferOpt[A1, A2, B1, B2] =
      tgt.RevTransferOpt(t)

    def project[C](p: Projection[|*|, B1 |*| B2, C]): ProjectRes[A1 |*| A2, C] =
      ProjectRes(asShuffle.project(p))

    def translate[->>[_, _], <*>[_, _], F[_, _], S1, S2](
      fa1: F[A1, S1],
      fa2: F[A2, S2],
      om: SemigroupalObjectMap[|*|, <*>, F],
    )(using
      tgt: libretto.lambda.Shuffled[->>, <*>],
    ): Exists[[T1] =>> Exists[[T2] =>> (tgt.RevTransferOpt[S1, S2, T1, T2], F[B1, T1], F[B2, T2])]] =
      t.translateRL(fa1, fa2)(om)(using tgt.shuffle) match
        case Exists.Some(Exists.Some((fb1, fb2, t1))) =>
          Exists(Exists((tgt.RevTransferOpt(t1), fb1, fb2)))

    def apply[F[_]](fa: F[A1 |*| A2])(using StrongZippable[|*|, F]): F[B1 |*| B2] =
      asShuffle.apply(fa)
  }

  def revDecompose1[X, Z1, Z2](f: X ~⚬ (Z1 |*| Z2)): RevDecomposition1[X, ?, ?, ?, ?, Z1, Z2] =
    ~⚬.decompose1(f.invert) match {
      case ~⚬.Decomposition1(f1, f2, g, ev) =>
        RevDecomposition1(ev.flip, RevTransferOpt(g), f1.invert, f2.invert)
    }

  case class RevDecomposition1[X, X1, X2, Y1, Y2, Z1, Z2](
    ev: X =:= (X1 |*| X2),
    t: RevTransferOpt[X1, X2, Y1, Y2],
    g1: Y1 ~⚬ Z1,
    g2: Y2 ~⚬ Z2,
  )

  def id[X]: Shuffled[X, X] =
    Permeable.id

  def id[X, Y](using ev: X =:= Y): Shuffled[X, Y] =
    ev.substituteCo(Permeable.id[X])

  def pure[X, Y](f: X ~⚬ Y): Shuffled[X, Y] =
    Pure(f)

  def fst[X, Y, Z](f: Shuffled[X, Y]): Shuffled[X |*| Z, Y |*| Z] =
    f.inFst[Z]

  def snd[X, Y, Z](f: Shuffled[Y, Z]): Shuffled[X |*| Y, X |*| Z] =
    f.inSnd[X]

  def par[X1, X2, Y1, Y2](f1: Shuffled[X1, Y1], f2: Shuffled[X2, Y2]): Shuffled[X1 |*| X2, Y1 |*| Y2] =
    fst(f1) > snd(f2)

  def assocLR[X, Y, Z]: Shuffled[(X |*| Y) |*| Z, X |*| (Y |*| Z)] =
    Pure(~⚬.assocLR)

  def assocRL[X, Y, Z]: Shuffled[X |*| (Y |*| Z), (X |*| Y) |*| Z] =
    Pure(~⚬.assocRL)

  def swap[X, Y]: Shuffled[X |*| Y, Y |*| X] =
    Pure(~⚬.swap)

  def ix[X, Y, Z]: Shuffled[(X |*| Y) |*| Z, (X |*| Z) |*| Y] =
    Pure(~⚬.ix)

  def xi[X, Y, Z]: Shuffled[X |*| (Y |*| Z), Y |*| (X |*| Z)] =
    Pure(~⚬.xi)

  def ixi[W, X, Y, Z]: Shuffled[(W |*| X) |*| (Y |*| Z), (W |*| Y) |*| (X |*| Z)] =
    Pure(~⚬.ixi)

  def lift[X, Y](f: X -> Y): Shuffled[X, Y] =
    Impermeable(~⚬.id, Solid(f), ~⚬.id)

  def fromForest[X, Y](f: AForest[->, |*|, X, Y]): Shuffled[X, Y] =
    import libretto.lambda.AForest.{Empty, Node, Par}

    f match
      case Empty()      => id
      case Node(f0, fs) => lift(f0) > fromForest(fs)
      case Par(f1, f2)  => par(fromForest(f1), fromForest(f2))

  def extractSnd[F[_], X, Y](i: Focus[|*|, F]): Shuffled[F[X |*| Y], F[X] |*| Y] =
    i match {
      case Focus.Id()    => id[X |*| Y]
      case Focus.Fst(i1) => extractSnd(i1).inFst > ix
      case Focus.Snd(i2) => extractSnd(i2).inSnd > assocRL
    }

  def absorbSnd[F[_], X, Y](i: Focus[|*|, F]): Shuffled[F[X] |*| Y, F[X |*| Y]] =
    i match {
      case Focus.Id()    => id[X |*| Y]
      case Focus.Fst(i1) => ix > fst(absorbSnd(i1))
      case Focus.Snd(i2) => assocLR > snd(absorbSnd(i2))
    }

  given SymmetricSemigroupalCategory[Shuffled, |*|] =
    new SymmetricSemigroupalCategory[Shuffled, |*|] {
      override def id[A]: Shuffled[A, A] = Shuffled.this.id
      override def andThen[A, B, C](f: Shuffled[A, B], g: Shuffled[B, C]): Shuffled[A, C] = f > g
      override def assocLR[A, B, C]: Shuffled[A |*| B |*| C, A |*| (B |*| C)] = Shuffled.this.assocLR
      override def assocRL[A, B, C]: Shuffled[A |*| (B |*| C), A |*| B |*| C] = Shuffled.this.assocRL
      override def par[A1, A2, B1, B2](f1: Shuffled[A1, B1], f2: Shuffled[A2, B2]): Shuffled[A1 |*| A2, B1 |*| B2] = Shuffled.this.par(f1, f2)
      override def swap[A, B]: Shuffled[A |*| B, B |*| A] = Shuffled.this.swap
    }

  private def ▄░▄[A1, A2, X2, Y2, B1, B2](
    l: Plated[A2, X2],
    m: (A1 |*| X2) ~⚬ (B1 |*| Y2),
    r: Plated[Y2, B2],
  ): Shuffled[A1 |*| A2, B1 |*| B2] =
    ~⚬.tryUntangle(m) match {
      case Right((m1, m2)) =>
        SemiObstructed(
          ~⚬.fst(m1),
          Plated.Sandwich(l, m2, r),
          ~⚬.id,
          TransferOpt.None(),
        )
      case Left(~⚬.Xfer(f1, f2, g)) =>
        Tr(g).`▄░_this_▄`(l, f1, f2, r)
    }

  /** Wrapper of [[Transfer]] to add additional virtual methods. */
  private sealed trait Tr[P1, P2, Q1, Q2] {
    def `▄░_this_▄`[A1, A2, X2, Z2](
      l: Plated[A2, X2],
      f1: A1 ~⚬ P1,
      f2: X2 ~⚬ P2,
      r: Plated[Q2, Z2],
    ): Shuffled[A1 |*| A2, Q1 |*| Z2]
  }

  private object Tr {
    case class Swap[P1, P2](value: Transfer.Swap[P1, P2]) extends Tr[P1, P2, P2, P1] {

      override def `▄░_this_▄`[A1, A2, X2, Z2](
        l: Plated[A2, X2],
        f1: A1 ~⚬ P1,
        f2: X2 ~⚬ P2,
        r: Plated[P1, Z2],
      ): Shuffled[A1 |*| A2, P2 |*| Z2] =
        Impermeable(
          ~⚬.fst(f1),
          Plated.Stacked(r, l),
          ~⚬.snd(f2) > ~⚬.swap,
        )

    }

    case class AssocLR[P1, P2, P3, Q2, Q3](value: Transfer.AssocLR[P1, P2, P3, Q2, Q3]) extends Tr[P1 |*| P2, P3, P1, Q2 |*| Q3] {

      override def `▄░_this_▄`[A1, A2, X2, Z2](
        l: Plated[A2, X2],
        f1: A1 ~⚬ (P1 |*| P2),
        f2: X2 ~⚬ P3,
        r: Plated[Q2 |*| Q3, Z2],
      ): Shuffled[A1 |*| A2, P1 |*| Z2] =
        SemiObstructed(
          ~⚬.fst(f1) > ~⚬.assocLR,
          Plated.SemiCons(l, f2, value.g, r),
          ~⚬.id,
          TransferOpt.None(),
        )

    }

    case class AssocRL[P1, P2, P3, Q1, Q2](value: Transfer.AssocRL[P1, P2, P3, Q1, Q2]) extends Tr[P1, P2 |*| P3, Q1 |*| Q2, P3] {

      override def `▄░_this_▄`[A1, A2, X2, Z2](
        l: Plated[A2, X2],
        f1: A1 ~⚬ P1,
        f2: X2 ~⚬ (P2 |*| P3),
        r: Plated[P3, Z2],
      ): Shuffled[A1 |*| A2, (Q1 |*| Q2) |*| Z2] =
        revDecompose1(f2) match {
          case RevDecomposition1(ev, t, g1, g2) =>
            SemiObstructed(
              ~⚬.fst(f1),
              Plated.SemiSnoc(ev.substituteCo(l), t, g2, r),
              ~⚬.fst(g1),
              Transfer.AssocRL(value.g),
            )
        }

    }

    case class IX[P1, P2, P3, Q1, Q2](value: Transfer.IX[P1, P2, P3, Q1, Q2]) extends Tr[P1 |*| P2, P3, Q1 |*| Q2, P2] {

      override def `▄░_this_▄`[A1, A2, X2, Z2](
        l: Plated[A2, X2],
        f1: A1 ~⚬ (P1 |*| P2),
        f2: X2 ~⚬ P3,
        r: Plated[P2, Z2],
      ): Shuffled[A1 |*| A2, (Q1 |*| Q2) |*| Z2] =
        Pure(~⚬.fst(f1) > ~⚬.assocLR) >
          snd(Impermeable(~⚬.swap, Plated.Stacked(l, r), ~⚬.fst(f2))) >
          Pure(~⚬.assocRL > ~⚬.fst(value.g.asShuffle))

    }

    case class XI[P1, P2, P3, Q2, Q3](value: Transfer.XI[P1, P2, P3, Q2, Q3]) extends Tr[P1, P2 |*| P3, P2, Q2 |*| Q3] {

      override def `▄░_this_▄`[A1, A2, X2, Z2](
        l: Plated[A2, X2],
        f1: A1 ~⚬ P1,
        f2: X2 ~⚬ (P2 |*| P3),
        r: Plated[Q2 |*| Q3, Z2],
      ): Shuffled[A1 |*| A2, P2 |*| Z2] =
        revDecompose1(f2) match {
          case RevDecomposition1(ev, g, h1, h2) =>
            Impermeable(~⚬.fst(f1), Plated.XI(ev.substituteCo(l), g, h2, value.g, r), ~⚬.fst(h1))
        }

    }

    case class IXI[P1, P2, P3, P4, Q1, Q2, Q3, Q4](value: Transfer.IXI[P1, P2, P3, P4, Q1, Q2, Q3, Q4]) extends Tr[P1 |*| P2, P3 |*| P4, Q1 |*| Q2, Q3 |*| Q4] {

      override def `▄░_this_▄`[A1, A2, X2, Z2](
        l: Plated[A2, X2],
        f1: A1 ~⚬ (P1 |*| P2),
        f2: X2 ~⚬ (P3 |*| P4),
        r: Plated[(Q3 |*| Q4), Z2],
      ): Shuffled[A1 |*| A2, (Q1 |*| Q2) |*| Z2] =
        revDecompose1(f2) match {
          case RevDecomposition1(ev, lt, f21, f22) =>
            ~⚬.decompose(value.g2.asShuffle) match {
              case ~⚬.Decomposition(g21, g22, rt) =>
                Pure(~⚬.fst(f1) > ~⚬.assocLR) >
                  snd(Impermeable(~⚬.fst(g21), Plated.XI(ev.substituteCo(l), lt, f22 > g22, rt, r), ~⚬.fst(f21))) >
                  Pure(~⚬.assocRL > ~⚬.fst(value.g1.asShuffle))
            }
        }

    }

    def apply[P1, P2, Q1, Q2](t: Transfer[P1, P2, Q1, Q2]): Tr[P1, P2, Q1, Q2] =
      t match {
        case t: Transfer.Swap[?, ?]                  => Swap(t)
        case t: Transfer.AssocLR[?, ?, ?, ?, ?]      => AssocLR(t)
        case t: Transfer.AssocRL[?, ?, ?, ?, ?]      => AssocRL(t)
        case t: Transfer.IX[?, ?, ?, ?, ?]           => IX(t)
        case t: Transfer.XI[?, ?, ?, ?, ?]           => XI(t)
        case t: Transfer.IXI[?, ?, ?, ?, ?, ?, ?, ?] => IXI(t)
      }
  }

  enum UnconsSomeRes[A, B] {
    case Pure(s: A ~⚬ B)

    case Cons[A, F[_], X, Y, B](
      pre: A ~⚬ F[X],
      i: Focus[|*|, F],
      f: X -> Y,
      post: Shuffled[F[Y], B],
    ) extends UnconsSomeRes[A, B]
  }

  /** A [[Shuffled]] with a hole through it. */
  trait Punched[F[_], G[_]] { self =>
    def focusIn: Focus[|*|, F]
    def focusOut: Focus[|*|, G]
    def plug[X]: Shuffled[F[X], G[X]]

    def apply[X]: Shuffled[F[X], G[X]] =
      plug[X]

    def >[H[_]](that: Punched[G, H]): Punched[F, H] =
      new Punched[F, H]:
        override def plug[X]: Shuffled[F[X], H[X]] = self.plug[X] > that.plug[X]
        override val focusIn = self.focusIn
        override val focusOut = that.focusOut

    def andThen[H[_]](H: Focus[|*|, H], h: [x] => Unit => Shuffled[G[x], H[x]]): Punched[F, H] =
      self > Punched(self.focusOut, H, h)

    def after[H[_]](H: Focus[|*|, H], h: [x] => Unit => Shuffled[H[x], F[x]]): Punched[H, G] =
      Punched(H, self.focusIn, h) > self

    def inFst[P, Q](g: Shuffled[P, Q]): Punched[[x] =>> F[x] |*| P, [x] =>> G[x] |*| Q] =
      new Punched[[x] =>> F[x] |*| P, [x] =>> G[x] |*| Q]:
        override def plug[X]: Shuffled[F[X] |*| P, G[X] |*| Q] = self.plug[X].inFst > snd(g)
        override val focusIn = self.focusIn.inFst[P]
        override val focusOut = self.focusOut.inFst[Q]

    def inFst[P]: Punched[[x] =>> F[x] |*| P, [x] =>> G[x] |*| P] =
      new Punched[[x] =>> F[x] |*| P, [x] =>> G[x] |*| P]:
        override def plug[X]: Shuffled[F[X] |*| P, G[X] |*| P] = self.plug[X].inFst
        override val focusIn = self.focusIn.inFst[P]
        override val focusOut = self.focusOut.inFst[P]

    def inSnd[P, Q](f: Shuffled[P, Q]): Punched[[x] =>> P |*| F[x], [x] =>> Q |*| G[x]] =
      new Punched[[x] =>> P |*| F[x], [x] =>> Q |*| G[x]]:
        override def plug[X]: Shuffled[P |*| F[X], Q |*| G[X]] = self.plug[X].inSnd > fst(f)
        override val focusIn = self.focusIn.inSnd[P]
        override val focusOut = self.focusOut.inSnd[Q]

    def inSnd[P]: Punched[[x] =>> P |*| F[x], [x] =>> P |*| G[x]] =
      new Punched[[x] =>> P |*| F[x], [x] =>> P |*| G[x]]:
        override def plug[X]: Shuffled[P |*| F[X], P |*| G[X]] = self.plug[X].inSnd
        override val focusIn = self.focusIn.inSnd[P]
        override val focusOut = self.focusOut.inSnd[P]

    def knitBw(k: Knit[|*|, G]): Exists[[F0] =>> (Knitted[|*|, F, F0], Shuffled[F0, k.Res])] =
      type FreshType
      val f: Shuffled[F[FreshType], G[FreshType]] = this.plug[FreshType]
      val p: Projection[|*|, G[FreshType], k.Res] = k.toProjection[FreshType]
      f.project(
        p,
        [x, y, z] => (op: x -> y, q: Projection[|*|, y, z]) =>
          throw AssertionError("Elimination of a fresh type cannot lead to projecting from operations"),
      ) match
        case res: ProjectRes.Projected[x, y, z] =>
          Knitted.fromProjection(res.p) match
            case Some(k0) =>
              val k1: Knitted[|*|, k0.T, x] = k0.value
              Exists((k1.asInstanceOf[Knitted[|*|, F, x]], res.f))
            case None =>
              throw AssertionError(s"Knitting was expected to result in a projection eliminating a single hole, got ${res.p}")
  }

  object Punched {
    def pure[F[_], G[_]](f: shuffle.~⚬.Punched[F, G]): Punched[F, G] =
      new Punched[F, G]:
        override def plug[X]: Shuffled[F[X], G[X]] = Pure(f.plug[X])
        override def focusIn: Focus[|*|, F] = f.focusIn
        override def focusOut: Focus[|*|, G] = f.focusOut

    def apply[F[_], G[_]](
      F: Focus[|*|, F],
      G: Focus[|*|, G],
      f: [x] => Unit => Shuffled[F[x], G[x]],
    ): Punched[F, G] =
      new Punched[F, G]:
        override def plug[X]: Shuffled[F[X], G[X]] = f[X](())
        override val focusIn = F
        override val focusOut = G

    def id[F[_]](f: Focus[|*|, F]): Punched[F, F] =
      new Punched[F, F]:
        override def plug[X]: Shuffled[F[X], F[X]] = Permeable.id[F[X]]
        override val focusIn = f
        override val focusOut = f
  }

  sealed trait ChaseFwRes[F[_], X, B] {
    def andThen[C](that: Shuffled[B, C]): ChaseFwRes[F, X, C]
    def thenSnd[B1, B2, C2](using B =:= (B1 |*| B2))(that: Shuffled[B2, C2]): ChaseFwRes[F, X, B1 |*| C2]
    def after[H[_]](H: Focus[|*|, H], h: [x] => Unit => Shuffled[H[x], F[x]]): ChaseFwRes[H, X, B]
    def inFst[C, D](snd: Shuffled[C, D]): ChaseFwRes[[x] =>> F[x] |*| C, X, B |*| D]
    def inSnd[P, Q](fst: Shuffled[P, Q]): ChaseFwRes[[x] =>> P |*| F[x], X, Q |*| B]

    def after[H[_]](h: Punched[H, F]): ChaseFwRes[H, X, B]   = after(h.focusIn, [x] => (_: Unit) => h.plug[x])
    def inFst[C]: ChaseFwRes[[x] =>> F[x] |*| C, X, B |*| C] = inFst(id[C])
    def inSnd[A]: ChaseFwRes[[x] =>> A |*| F[x], X, A |*| B] = inSnd(id[A])
  }

  object ChaseFwRes {
    case class Transported[F[_], X, G[_], B](
      s: Punched[F, G],
      ev: G[X] =:= B,
    ) extends ChaseFwRes[F, X, B] {
      override def after[H[_]](H: Focus[|*|, H], h: [x] => (x: Unit) => Shuffled[H[x], F[x]]): ChaseFwRes[H, X, B] =
        Transported(s.after(H, h), ev)

      override def andThen[C](that: Shuffled[B, C]): ChaseFwRes[F, X, C] =
        that.chaseFw[G, X](s.focusOut)(using ev.flip).after(s)

      override def thenSnd[B1, B2, C2](using ev1: B =:= (B1 |*| B2))(that: Shuffled[B2, C2]): ChaseFwRes[F, X, B1 |*| C2] =
        s.focusOut match {
          case g: Focus.Fst[pair, g1, b2] =>
            (summon[(g1[X] |*| b2) =:= G[X]] andThen ev andThen ev1) match
              case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                Transported[F, X, [x] =>> g1[x] |*| C2, B1 |*| C2](
                  Punched(
                    s.focusIn,
                    g.i.inFst[C2],
                    [x] => (_: Unit) => s[x] > that.inSnd[g1[x]],
                  ),
                  summon,
                )
          case g: Focus.Snd[pair, g2, b1] =>
            (summon[(b1 |*| g2[X]) =:= G[X]] andThen ev andThen ev1) match
              case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                that.chaseFw[g2, X](g.i).inSnd[B1].after(s)
          case Focus.Id() =>
            Split(ev andThen ev1)
        }

      override def inFst[C, D](snd: Shuffled[C, D]): ChaseFwRes[[x] =>> F[x] |*| C, X, B |*| D] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.inFst")

      override def inSnd[P, Q](fst: Shuffled[P, Q]): ChaseFwRes[[x] =>> P |*| F[x], X, Q |*| B] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.inSnd")
    }

    sealed trait Blocked[F[_], X, B] extends ChaseFwRes[F, X, B] {
      infix def andThen[C](that: Shuffled[B, C]): ChaseFwRes.Blocked[F, X, C]
      infix def after[H[_]](H: Focus[|*|, H], h: [x] => Unit => Shuffled[H[x], F[x]]): ChaseFwRes.Blocked[H, X, B]
      def inFst[C, D](snd: Shuffled[C, D]): ChaseFwRes.Blocked[[x] =>> F[x] |*| C, X, B |*| D]
      def inSnd[P, Q](fst: Shuffled[P, Q]): ChaseFwRes.Blocked[[x] =>> P |*| F[x], X, Q |*| B]

      override def after[H[_]](h: Punched[H, F]): ChaseFwRes.Blocked[H, X, B]   = after(h.focusIn, [x] => (_: Unit) => h.plug[x])
      override def inFst[C]: ChaseFwRes.Blocked[[x] =>> F[x] |*| C, X, B |*| C] = inFst(id[C])
      override def inSnd[A]: ChaseFwRes.Blocked[[x] =>> A |*| F[x], X, A |*| B] = inSnd(id[A])
    }

    case class FedTo[F[_], X, V[_], W, G[_], B](
      pre: Punched[F, [x] =>> G[V[x]]],
      v: Focus[|*|, V],
      f: V[X] -> W,
      g: Focus[|*|, G],
      post: Shuffled[G[W], B],
    ) extends ChaseFwRes.Blocked[F, X, B] {
      override def after[H[_]](H: Focus[|*|, H], h: [x] => (x: Unit) => Shuffled[H[x], F[x]]): ChaseFwRes.Blocked[H, X, B] =
        FedTo(pre.after(H, h), v, f, g, post)

      override def andThen[C](that: Shuffled[B, C]): ChaseFwRes.Blocked[F, X, C] =
        FedTo(pre, v, f, g, post > that)

      override def thenSnd[B1, B2, C2](using B =:= (B1 |*| B2))(that: Shuffled[B2, C2]): ChaseFwRes[F, X, B1 |*| C2] =
        FedTo(pre, v, f, g, post.to[B1 |*| B2] > snd(that))

      override def inFst[C, D](snd: Shuffled[C, D]): Blocked[[x] =>> F[x] |*| C, X, B |*| D] =
        FedTo[[x] =>> F[x] |*| C, X, V, W, [x] =>> G[x] |*| C, B |*| D](
          pre.inFst[C],
          v,
          f,
          g.inFst[C],
          par(post, snd),
        )

      override def inSnd[P, Q](fst: Shuffled[P, Q]): ChaseFwRes.Blocked[[x] =>> P |*| F[x], X, Q |*| B] =
        FedTo[[x] =>> P |*| F[x], X, V, W, [x] =>> P |*| G[x], Q |*| B](
          pre.inSnd[P],
          v,
          f,
          g.inSnd[P],
          par(fst, post),
        )
    }

    case class Split[F[_], X, X1, X2, B](ev: X =:= (X1 |*| X2)) extends ChaseFwRes.Blocked[F, X, B] {
      override def after[H[_]](H: Focus[|*|, H], h: [x] => (x: Unit) => Shuffled[H[x], F[x]]): ChaseFwRes.Blocked[H, X, B] = Split(ev)
      override def andThen[C](that: Shuffled[B, C]): Blocked[F, X, C] = Split(ev)
      override def thenSnd[B1, B2, C2](using B =:= (B1 |*| B2))(that: Shuffled[B2, C2]): ChaseFwRes[F, X, B1 |*| C2] = Split(ev)
      override def inFst[C, D](snd: Shuffled[C, D]): Blocked[[x] =>> F[x] |*| C, X, B |*| D] = Split(ev)
      override def inSnd[P, Q](fst: Shuffled[P, Q]): Blocked[[x] =>> P |*| F[x], X, Q |*| B] = Split(ev)
    }

    def apply[F[_], X, B](r: ~⚬.ChaseFwRes[F, X, B]): ChaseFwRes[F, X, B] =
      r match
        case ~⚬.ChaseFwRes.Transported(s, ev) => Transported(Punched.pure(s), ev)
        case ~⚬.ChaseFwRes.Split(ev)          => Split(ev)
  }

  sealed trait ChaseBwRes[A, G[_], X] {
    def after[P](p: Shuffled[P, A]): ChaseBwRes[P, G, X]
    def andThen[H[_]](H: Focus[|*|, H], h: [x] => Unit => Shuffled[G[x], H[x]]): ChaseBwRes[A, H, X]
    def inFst[P, Q](snd: Shuffled[P, Q]): ChaseBwRes[A |*| P, [x] =>> G[x] |*| Q, X]
    def inSnd[P, Q](fst: Shuffled[P, Q]): ChaseBwRes[P |*| A, [x] =>> Q |*| G[x], X]

    def andThen[H[_]](h: Punched[G, H]): ChaseBwRes[A, H, X] = andThen(h.focusOut, [x] => (_: Unit) => h.plug[x])
    def inFst[Q]: ChaseBwRes[A |*| Q, [x] =>> G[x] |*| Q, X] = inFst(id[Q])
    def inSnd[P]: ChaseBwRes[P |*| A, [x] =>> P |*| G[x], X] = inSnd(id[P])
  }

  object ChaseBwRes {
    case class Transported[A, F[_], G[_], X](
      ev: A =:= F[X],
      s: Punched[F, G],
    ) extends ChaseBwRes[A, G, X] {
      override def after[P](p: Shuffled[P, A]): ChaseBwRes[P, G, X] =
        p.chaseBw[F, X](s.focusIn)(using ev).andThen(s)

      override def andThen[H[_]](H: Focus[|*|, H], h: [x] => (x: Unit) => Shuffled[G[x], H[x]]): ChaseBwRes[A, H, X] =
        Transported[A, F, H, X](ev, s.andThen(H, h))

      override def inFst[P, Q](snd: Shuffled[P, Q]): ChaseBwRes[A |*| P, [x] =>> G[x] |*| Q, X] =
        Transported[A |*| P, [x] =>> F[x] |*| P, [x] =>> G[x] |*| Q, X](
          ev zipEq summon[P =:= P],
          s.inFst(snd),
        )

      override def inSnd[P, Q](fst: Shuffled[P, Q]): ChaseBwRes[P |*| A, [x] =>> Q |*| G[x], X] =
        Transported[P |*| A, [x] =>> P |*| F[x], [x] =>> Q |*| G[x], X](
          summon[P =:= P] zipEq ev,
          s.inSnd(fst),
        )
    }

    sealed trait Blocked[A, G[_], X] extends ChaseBwRes[A, G, X] {
      infix override def after[P](p: Shuffled[P, A]): ChaseBwRes.Blocked[P, G, X]
      infix override def andThen[H[_]](H: Focus[|*|, H], h: [x] => Unit => Shuffled[G[x], H[x]]): ChaseBwRes.Blocked[A, H, X]
      override def inFst[P, Q](snd: Shuffled[P, Q]): ChaseBwRes.Blocked[A |*| P, [x] =>> G[x] |*| Q, X]
      override def inSnd[P, Q](fst: Shuffled[P, Q]): ChaseBwRes.Blocked[P |*| A, [x] =>> Q |*| G[x], X]

      override def andThen[H[_]](h: Punched[G, H]): ChaseBwRes.Blocked[A, H, X] = andThen(h.focusOut, [x] => (_: Unit) => h.plug[x])
      override def inFst[Q]: ChaseBwRes.Blocked[A |*| Q, [x] =>> G[x] |*| Q, X] = inFst(id[Q])
      override def inSnd[P]: ChaseBwRes.Blocked[P |*| A, [x] =>> P |*| G[x], X] = inSnd(id[P])
    }

    case class OriginatesFrom[A, F[_], V, W[_], X, G[_]](
      pre: Shuffled[A, F[V]],
      i: Focus[|*|, F],
      f: V -> W[X],
      w: Focus[|*|, W],
      post: Punched[[x] =>> F[W[x]], G],
    ) extends ChaseBwRes.Blocked[A, G, X] {
      override def after[P](p: Shuffled[P, A]): ChaseBwRes.Blocked[P, G, X] =
        OriginatesFrom(p > pre, i, f, w, post)

      override def andThen[H[_]](H: Focus[|*|, H], h: [x] => Unit => Shuffled[G[x], H[x]]): Blocked[A, H, X] =
        OriginatesFrom(pre, i, f, w, post.andThen(H, h))

      override def inFst[P, Q](snd: Shuffled[P, Q]): ChaseBwRes.Blocked[A |*| P, [x] =>> G[x] |*| Q, X] =
        OriginatesFrom[A |*| P, [t] =>> F[t] |*| Q, V, W, X, [x] =>> G[x] |*| Q](par(pre, snd), i.inFst, f, w, post.inFst)

      override def inSnd[P, Q](fst: Shuffled[P, Q]): ChaseBwRes.Blocked[P |*| A, [x] =>> Q |*| G[x], X] =
        OriginatesFrom[P |*| A, [t] =>> Q |*| F[t], V, W, X, [x] =>> Q |*| G[x]](par(fst, pre), i.inSnd, f, w, post.inSnd)
    }

    case class Split[A, G[_], X, X1, X2](ev: X =:= (X1 |*| X2)) extends ChaseBwRes.Blocked[A, G, X] {
      override def after[P](p: Shuffled[P, A]): ChaseBwRes.Blocked[P, G, X] = Split(ev)
      override def andThen[H[_]](H: Focus[|*|, H], h: [x] => Unit => Shuffled[G[x], H[x]]): Blocked[A, H, X] = Split(ev)
      override def inFst[P, Q](snd: Shuffled[P, Q]): ChaseBwRes.Blocked[A |*| P, [x] =>> G[x] |*| Q, X] = Split(ev)
      override def inSnd[P, Q](fst: Shuffled[P, Q]): ChaseBwRes.Blocked[P |*| A, [x] =>> Q |*| G[x], X] = Split(ev)
    }

    def apply[A, G[_], X](r: ~⚬.ChaseBwRes[A, G, X]): ChaseBwRes[A, G, X] =
      r match
        case ~⚬.ChaseBwRes.Split(ev)          => Split(ev)
        case ~⚬.ChaseBwRes.Transported(ev, s) => Transported(ev, Punched.pure(s))
  }

  enum ProjectRes[A, C] {
    case Projected[A0, A, C](p: Projection[|*|, A, A0], f: Shuffled[A0, C]) extends ProjectRes[A, C]

    def project[D](
      q: Projection[|*|, C, D],
      h: [X, Y, Z] => (X -> Y, Projection[|*|, Y, Z]) => ProjectRes[X, Z],
    ): ProjectRes[A, D] =
      this match {
        case Projected(p, f) =>
          f.project(q, h) match
            case Projected(p1, f1) => Projected(p > p1, f1)
      }

    def inFst[Y, Z](snd: Shuffled[Y, Z]): ProjectRes[A |*| Y, C |*| Z] =
      this match { case Projected(p, f) => Projected(p.inFst[Y], par(f, snd)) }

    def inFst[Y]: ProjectRes[A |*| Y, C |*| Y] =
      inFst(id[Y])

    def inSnd[X, Y](fst: Shuffled[X, Y]): ProjectRes[X |*| A, Y |*| C] =
      this match { case Projected(p, f) => Projected(p.inSnd[X], par(fst, f)) }

    def inSnd[X]: ProjectRes[X |*| A, X |*| C] =
      inSnd(id[X])

    def after[Z](f: Shuffled[Z, A], h: [P, Q, R] => (P -> Q, Projection[|*|, Q, R]) => ProjectRes[P, R]): ProjectRes[Z, C] =
      this match
        case Projected(p, g) =>
          f.project(p, h) match
            case Projected(p0, f0) => Projected(p0, f0 > g)

    def andThen[D](g: Shuffled[C, D]): ProjectRes[A, D] =
      this match
        case Projected(p, f) => Projected(p, f > g)

    def to[D](using ev: C =:= D): ProjectRes[A, D] =
      ev.substituteCo(this)
  }

  object ProjectRes {
    def apply[A, C](r: ~⚬.ProjectRes[A, C]): ProjectRes[A, C] =
      r match
        case ~⚬.ProjectRes.Projected(p, f) =>
          Projected(p, Pure(f))

    def apply[A, C](r: ~⚬.ProjectProperRes[A, C]): ProjectRes[A, C] =
      ProjectRes(r.unproper)
  }
}
