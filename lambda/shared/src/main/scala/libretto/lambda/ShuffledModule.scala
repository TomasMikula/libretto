package libretto.lambda

import libretto.lambda.util.{Applicative, BiInjective, Exists, TypeEq}
import libretto.lambda.util.TypeEq.Refl

trait ShuffledModule[->[_, _], **[_, _]] { self =>
  given biInjectivePair: BiInjective[**]
  val shuffle: Shuffle[**]
  import shuffle.{~⚬, zip as zipEq}

  type Shuffled[A, B]

  /** A [[Shuffled]] with a hole through it. */
  type Punched[F[_], G[_]]

  def id[A]: Shuffled[A, A]
  def andThen[A, B, C](f: Shuffled[A, B], g: Shuffled[B, C]): Shuffled[A, C]
  def par[A1, A2, B1, B2](f1: Shuffled[A1, B1], f2: Shuffled[A2, B2]): Shuffled[A1 ** A2, B1 ** B2]
  def fst[A, B, C](f: Shuffled[A, B]): Shuffled[A ** C, B ** C]
  def snd[A, B, C](f: Shuffled[B, C]): Shuffled[A ** B, A ** C]
  def assocLR[A, B, C]: Shuffled[(A ** B) ** C, A ** (B ** C)]
  def assocRL[A, B, C]: Shuffled[A ** (B ** C), (A ** B) ** C]
  def swap[A, B]: Shuffled[A ** B, B ** A]
  def ix[A, B, C]: Shuffled[(A ** B) ** C, (A ** C) ** B]
  def xi[A, B, C]: Shuffled[A ** (B ** C), B ** (A ** C)]
  def ixi[A, B, C, D]: Shuffled[(A ** B) ** (C ** D), (A ** C) ** (B ** D)]

  def lift[X, Y](f: X -> Y): Shuffled[X, Y]
  def pure[A, B](f: A ~⚬ B): Shuffled[A, B]

  val Punched: PunchedCompanion

  trait PunchedCompanion {
    def apply[F[_], G[_]](
      F: Focus[**, F],
      G: Focus[**, G],
      f: [x] => Unit => Shuffled[F[x], G[x]],
    ): Punched[F, G]

    def pure[F[_], G[_]](f: shuffle.~⚬.Punched[F, G]): Punched[F, G] =
      Punched(f.focusIn, f.focusOut, [X] => (_: Unit) => self.pure(f.plug[X]))
  }

  extension [A, B](f: Shuffled[A, B]) {
    def foldMap[->>[_, _]](h: [x, y] => (x -> y) => (x ->> y))(using SymmetricSemigroupalCategory[->>, **]): A ->> B

    def fold(using SymmetricSemigroupalCategory[->, **]): A -> B =
      foldMap[->]([x, y] => (f: x -> y) => f)

    def foldMapA[G[_], ->>[_, _]](
      h: [t, u] => (t -> u) => G[t ->> u],
    )(using
      G: Applicative[G],
      cat: SymmetricSemigroupalCategory[->>, **],
    ): G[A ->> B] =
      foldMap[[a, b] =>> G[a ->> b]](h)(using cat.hoist[G])

    def project[C](
      p: Projection[**, B, C],
      h: [X, Y, Z] => (X -> Y, Projection[**, Y, Z]) => ProjectRes[X, Z],
    ): ProjectRes[A, C]

    def chaseFw[F[_], X](i: Focus[**, F])(using A =:= F[X]): ChaseFwRes[F, X, B]

    def chaseBw[G[_], X](i: Focus[**, G])(using B =:= G[X]): ChaseBwRes[A, G, X]

    /** Extracts the maximum forest-shaped prefix
     * at the given position satisfying the given predicate.
     */
    def takeLeadingForestAtWhile[F[_], X, ->>[_, _]](
      pos: Focus[**, F],
      pred: [x, y] => (x -> y) => Option[x ->> y],
    )(using
      ev: A =:= F[X],
    ): Exists[[Y] =>> (AForest[->>, **, X, Y], Shuffled[F[Y], B])]

    /** Extracts the maximum forest-shaped prefix at the given position. */
    def takeLeadingForestAt[F[_], X](
      pos: Focus[**, F],
    )(using
      ev: A =:= F[X],
    ): Exists[[Y] =>> (AForest[->, **, X, Y], Shuffled[F[Y], B])] =
      takeLeadingForestAtWhile[F, X, ->](
        pos,
        [x, y] => (f: x -> y) => Some(f),
      )
  }

  given SymmetricSemigroupalCategory[Shuffled, **] with {
    override def id[A]: Shuffled[A, A] =
      self.id[A]

    override def andThen[A, B, C](f: Shuffled[A, B], g: Shuffled[B, C]): Shuffled[A, C] =
      self.andThen(f, g)

    override def par[X1, X2, Y1, Y2](
      f1: Shuffled[X1, Y1],
      f2: Shuffled[X2, Y2],
    ): Shuffled[X1 ** X2, Y1 ** Y2] =
        self.par(f1, f2)

    override def fst[A, B, C](f: Shuffled[A, B]): Shuffled[A ** C, B ** C] =
      self.fst(f)

    override def snd[A, B, C](f: Shuffled[B, C]): Shuffled[A ** B, A ** C] =
      self.snd(f)

    override def assocLR[A, B, C]: Shuffled[(A ** B) ** C, A ** (B ** C)] =
      self.assocLR

    override def assocRL[A, B, C]: Shuffled[A ** (B ** C), (A ** B) ** C] =
      self.assocRL

    override def swap[A, B]: Shuffled[A ** B, B ** A] =
      self.swap

    override def ix[A, B, C]: Shuffled[(A ** B) ** C, (A ** C) ** B] =
      self.ix

    override def xi[A, B, C]: Shuffled[A ** (B ** C), B ** (A ** C)] =
      self.xi

    override def ixi[A, B, C, D]: Shuffled[(A ** B) ** (C ** D), (A ** C) ** (B ** D)] =
      self.ixi
  }

  enum ProjectRes[A, C] {
    case Projected[A0, A, C](p: Projection[**, A, A0], f: Shuffled[A0, C]) extends ProjectRes[A, C]

    def project[D](
      q: Projection[**, C, D],
      h: [X, Y, Z] => (X -> Y, Projection[**, Y, Z]) => ProjectRes[X, Z],
    ): ProjectRes[A, D] =
      this match {
        case Projected(p, f) =>
          f.project(q, h) match
            case Projected(p1, f1) => Projected(p > p1, f1)
      }

    def inFst[Y, Z](snd: Shuffled[Y, Z]): ProjectRes[A ** Y, C ** Z] =
      this match { case Projected(p, f) => Projected(p.inFst[Y], par(f, snd)) }

    def inFst[Y]: ProjectRes[A ** Y, C ** Y] =
      inFst(id[Y])

    def inSnd[X, Y](fst: Shuffled[X, Y]): ProjectRes[X ** A, Y ** C] =
      this match { case Projected(p, f) => Projected(p.inSnd[X], par(fst, f)) }

    def inSnd[X]: ProjectRes[X ** A, X ** C] =
      inSnd(id[X])

    def after[Z](f: Shuffled[Z, A], h: [P, Q, R] => (P -> Q, Projection[**, Q, R]) => ProjectRes[P, R]): ProjectRes[Z, C] =
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
          Projected(p, pure(f))

    def apply[A, C](r: ~⚬.ProjectProperRes[A, C]): ProjectRes[A, C] =
      ProjectRes(r.unproper)
  }


  sealed trait ChaseFwRes[F[_], X, B] {
    def andThen[C](that: Shuffled[B, C]): ChaseFwRes[F, X, C]
    def thenSnd[B1, B2, C2](using B =:= (B1 ** B2))(that: Shuffled[B2, C2]): ChaseFwRes[F, X, B1 ** C2]
    def after[H[_]](H: Focus[**, H], h: [x] => Unit => Shuffled[H[x], F[x]]): ChaseFwRes[H, X, B]
    def inFst[C, D](snd: Shuffled[C, D]): ChaseFwRes[[x] =>> F[x] ** C, X, B ** D]
    def inSnd[P, Q](fst: Shuffled[P, Q]): ChaseFwRes[[x] =>> P ** F[x], X, Q ** B]

    def after[H[_]](h: Punched[H, F]): ChaseFwRes[H, X, B]   = after(h.focusIn, [x] => (_: Unit) => h.plug[x])
    def inFst[C]: ChaseFwRes[[x] =>> F[x] ** C, X, B ** C] = inFst(id[C])
    def inSnd[A]: ChaseFwRes[[x] =>> A ** F[x], X, A ** B] = inSnd(id[A])
  }

  object ChaseFwRes {
    case class Transported[F[_], X, G[_], B](
      s: Punched[F, G],
      ev: G[X] =:= B,
    ) extends ChaseFwRes[F, X, B] {
      override def after[H[_]](H: Focus[**, H], h: [x] => (x: Unit) => Shuffled[H[x], F[x]]): ChaseFwRes[H, X, B] =
        Transported(s.after(H, h), ev)

      override def andThen[C](that: Shuffled[B, C]): ChaseFwRes[F, X, C] =
        that.chaseFw[G, X](s.focusOut)(using ev.flip).after(s)

      override def thenSnd[B1, B2, C2](using ev1: B =:= (B1 ** B2))(that: Shuffled[B2, C2]): ChaseFwRes[F, X, B1 ** C2] =
        s.focusOut match {
          case g: Focus.Fst[pair, g1, b2] =>
            (summon[(g1[X] ** b2) =:= G[X]] andThen ev andThen ev1) match
              case BiInjective[**](TypeEq(Refl()), TypeEq(Refl())) =>
                Transported[F, X, [x] =>> g1[x] ** C2, B1 ** C2](
                  Punched(
                    s.focusIn,
                    g.i.inFst[C2],
                    [x] => (_: Unit) => s.plug[x] > that.inSnd[g1[x]],
                  ),
                  summon,
                )
          case g: Focus.Snd[pair, g2, b1] =>
            (summon[(b1 ** g2[X]) =:= G[X]] andThen ev andThen ev1) match
              case BiInjective[**](TypeEq(Refl()), TypeEq(Refl())) =>
                that.chaseFw[g2, X](g.i).inSnd[B1].after(s)
          case Focus.Id() =>
            Split(ev andThen ev1)
        }

      override def inFst[C, D](snd: Shuffled[C, D]): ChaseFwRes[[x] =>> F[x] ** C, X, B ** D] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.inFst")

      override def inSnd[P, Q](fst: Shuffled[P, Q]): ChaseFwRes[[x] =>> P ** F[x], X, Q ** B] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.inSnd")
    }

    sealed trait Blocked[F[_], X, B] extends ChaseFwRes[F, X, B] {
      infix def andThen[C](that: Shuffled[B, C]): ChaseFwRes.Blocked[F, X, C]
      infix def after[H[_]](H: Focus[**, H], h: [x] => Unit => Shuffled[H[x], F[x]]): ChaseFwRes.Blocked[H, X, B]
      def inFst[C, D](snd: Shuffled[C, D]): ChaseFwRes.Blocked[[x] =>> F[x] ** C, X, B ** D]
      def inSnd[P, Q](fst: Shuffled[P, Q]): ChaseFwRes.Blocked[[x] =>> P ** F[x], X, Q ** B]

      override def after[H[_]](h: Punched[H, F]): ChaseFwRes.Blocked[H, X, B]   = after(h.focusIn, [x] => (_: Unit) => h.plug[x])
      override def inFst[C]: ChaseFwRes.Blocked[[x] =>> F[x] ** C, X, B ** C] = inFst(id[C])
      override def inSnd[A]: ChaseFwRes.Blocked[[x] =>> A ** F[x], X, A ** B] = inSnd(id[A])
    }

    case class FedTo[F[_], X, V[_], W, G[_], B](
      pre: Punched[F, [x] =>> G[V[x]]],
      v: Focus[**, V],
      f: V[X] -> W,
      g: Focus[**, G],
      post: Shuffled[G[W], B],
    ) extends ChaseFwRes.Blocked[F, X, B] {
      override def after[H[_]](H: Focus[**, H], h: [x] => (x: Unit) => Shuffled[H[x], F[x]]): ChaseFwRes.Blocked[H, X, B] =
        FedTo(pre.after(H, h), v, f, g, post)

      override def andThen[C](that: Shuffled[B, C]): ChaseFwRes.Blocked[F, X, C] =
        FedTo(pre, v, f, g, post > that)

      override def thenSnd[B1, B2, C2](using B =:= (B1 ** B2))(that: Shuffled[B2, C2]): ChaseFwRes[F, X, B1 ** C2] =
        FedTo(pre, v, f, g, post.to[B1 ** B2] > snd(that))

      override def inFst[C, D](snd: Shuffled[C, D]): Blocked[[x] =>> F[x] ** C, X, B ** D] =
        FedTo[[x] =>> F[x] ** C, X, V, W, [x] =>> G[x] ** C, B ** D](
          pre.inFst[C],
          v,
          f,
          g.inFst[C],
          par(post, snd),
        )

      override def inSnd[P, Q](fst: Shuffled[P, Q]): ChaseFwRes.Blocked[[x] =>> P ** F[x], X, Q ** B] =
        FedTo[[x] =>> P ** F[x], X, V, W, [x] =>> P ** G[x], Q ** B](
          pre.inSnd[P],
          v,
          f,
          g.inSnd[P],
          par(fst, post),
        )
    }

    case class Split[F[_], X, X1, X2, B](ev: X =:= (X1 ** X2)) extends ChaseFwRes.Blocked[F, X, B] {
      override def after[H[_]](H: Focus[**, H], h: [x] => (x: Unit) => Shuffled[H[x], F[x]]): ChaseFwRes.Blocked[H, X, B] = Split(ev)
      override def andThen[C](that: Shuffled[B, C]): Blocked[F, X, C] = Split(ev)
      override def thenSnd[B1, B2, C2](using B =:= (B1 ** B2))(that: Shuffled[B2, C2]): ChaseFwRes[F, X, B1 ** C2] = Split(ev)
      override def inFst[C, D](snd: Shuffled[C, D]): Blocked[[x] =>> F[x] ** C, X, B ** D] = Split(ev)
      override def inSnd[P, Q](fst: Shuffled[P, Q]): Blocked[[x] =>> P ** F[x], X, Q ** B] = Split(ev)
    }

    def apply[F[_], X, B](r: ~⚬.ChaseFwRes[F, X, B]): ChaseFwRes[F, X, B] =
      r match
        case ~⚬.ChaseFwRes.Transported(s, ev) => Transported(Punched.pure(s), ev)
        case ~⚬.ChaseFwRes.Split(ev)          => Split(ev)
  }

  sealed trait ChaseBwRes[A, G[_], X] {
    def after[P](p: Shuffled[P, A]): ChaseBwRes[P, G, X]
    def andThen[H[_]](H: Focus[**, H], h: [x] => Unit => Shuffled[G[x], H[x]]): ChaseBwRes[A, H, X]
    def inFst[P, Q](snd: Shuffled[P, Q]): ChaseBwRes[A ** P, [x] =>> G[x] ** Q, X]
    def inSnd[P, Q](fst: Shuffled[P, Q]): ChaseBwRes[P ** A, [x] =>> Q ** G[x], X]

    def andThen[H[_]](h: Punched[G, H]): ChaseBwRes[A, H, X] = andThen(h.focusOut, [x] => (_: Unit) => h.plug[x])
    def inFst[Q]: ChaseBwRes[A ** Q, [x] =>> G[x] ** Q, X] = inFst(id[Q])
    def inSnd[P]: ChaseBwRes[P ** A, [x] =>> P ** G[x], X] = inSnd(id[P])
  }

  object ChaseBwRes {
    case class Transported[A, F[_], G[_], X](
      ev: A =:= F[X],
      s: Punched[F, G],
    ) extends ChaseBwRes[A, G, X] {
      override def after[P](p: Shuffled[P, A]): ChaseBwRes[P, G, X] =
        p.chaseBw[F, X](s.focusIn)(using ev).andThen(s)

      override def andThen[H[_]](H: Focus[**, H], h: [x] => (x: Unit) => Shuffled[G[x], H[x]]): ChaseBwRes[A, H, X] =
        Transported[A, F, H, X](ev, s.andThen(H, h))

      override def inFst[P, Q](snd: Shuffled[P, Q]): ChaseBwRes[A ** P, [x] =>> G[x] ** Q, X] =
        Transported[A ** P, [x] =>> F[x] ** P, [x] =>> G[x] ** Q, X](
          ev zipEq summon[P =:= P],
          s.inFst(snd),
        )

      override def inSnd[P, Q](fst: Shuffled[P, Q]): ChaseBwRes[P ** A, [x] =>> Q ** G[x], X] =
        Transported[P ** A, [x] =>> P ** F[x], [x] =>> Q ** G[x], X](
          summon[P =:= P] zipEq ev,
          s.inSnd(fst),
        )
    }

    sealed trait Blocked[A, G[_], X] extends ChaseBwRes[A, G, X] {
      infix override def after[P](p: Shuffled[P, A]): ChaseBwRes.Blocked[P, G, X]
      infix override def andThen[H[_]](H: Focus[**, H], h: [x] => Unit => Shuffled[G[x], H[x]]): ChaseBwRes.Blocked[A, H, X]
      override def inFst[P, Q](snd: Shuffled[P, Q]): ChaseBwRes.Blocked[A ** P, [x] =>> G[x] ** Q, X]
      override def inSnd[P, Q](fst: Shuffled[P, Q]): ChaseBwRes.Blocked[P ** A, [x] =>> Q ** G[x], X]

      override def andThen[H[_]](h: Punched[G, H]): ChaseBwRes.Blocked[A, H, X] = andThen(h.focusOut, [x] => (_: Unit) => h.plug[x])
      override def inFst[Q]: ChaseBwRes.Blocked[A ** Q, [x] =>> G[x] ** Q, X] = inFst(id[Q])
      override def inSnd[P]: ChaseBwRes.Blocked[P ** A, [x] =>> P ** G[x], X] = inSnd(id[P])
    }

    case class OriginatesFrom[A, F[_], V, W[_], X, G[_]](
      pre: Shuffled[A, F[V]],
      i: Focus[**, F],
      f: V -> W[X],
      w: Focus[**, W],
      post: Punched[[x] =>> F[W[x]], G],
    ) extends ChaseBwRes.Blocked[A, G, X] {
      override def after[P](p: Shuffled[P, A]): ChaseBwRes.Blocked[P, G, X] =
        OriginatesFrom(p > pre, i, f, w, post)

      override def andThen[H[_]](H: Focus[**, H], h: [x] => Unit => Shuffled[G[x], H[x]]): Blocked[A, H, X] =
        OriginatesFrom(pre, i, f, w, post.andThen(H, h))

      override def inFst[P, Q](snd: Shuffled[P, Q]): ChaseBwRes.Blocked[A ** P, [x] =>> G[x] ** Q, X] =
        OriginatesFrom[A ** P, [t] =>> F[t] ** Q, V, W, X, [x] =>> G[x] ** Q](par(pre, snd), i.inFst, f, w, post.inFst)

      override def inSnd[P, Q](fst: Shuffled[P, Q]): ChaseBwRes.Blocked[P ** A, [x] =>> Q ** G[x], X] =
        OriginatesFrom[P ** A, [t] =>> Q ** F[t], V, W, X, [x] =>> Q ** G[x]](par(fst, pre), i.inSnd, f, w, post.inSnd)
    }

    case class Split[A, G[_], X, X1, X2](ev: X =:= (X1 ** X2)) extends ChaseBwRes.Blocked[A, G, X] {
      override def after[P](p: Shuffled[P, A]): ChaseBwRes.Blocked[P, G, X] = Split(ev)
      override def andThen[H[_]](H: Focus[**, H], h: [x] => Unit => Shuffled[G[x], H[x]]): Blocked[A, H, X] = Split(ev)
      override def inFst[P, Q](snd: Shuffled[P, Q]): ChaseBwRes.Blocked[A ** P, [x] =>> G[x] ** Q, X] = Split(ev)
      override def inSnd[P, Q](fst: Shuffled[P, Q]): ChaseBwRes.Blocked[P ** A, [x] =>> Q ** G[x], X] = Split(ev)
    }

    def apply[A, G[_], X](r: ~⚬.ChaseBwRes[A, G, X]): ChaseBwRes[A, G, X] =
      r match
        case ~⚬.ChaseBwRes.Split(ev)          => Split(ev)
        case ~⚬.ChaseBwRes.Transported(ev, s) => Transported(ev, Punched.pure(s))
  }

  extension [F[_], G[_]](p: Punched[F, G]) {
    def focusIn: Focus[**, F]
    def focusOut: Focus[**, G]
    def plug[X]: Shuffled[F[X], G[X]]
    def knitBw(k: Knit[**, G]): Exists[[F0] =>> (Knitted[**, F, F0], Shuffled[F0, k.Res])]

    def >[H[_]](that: Punched[G, H]): Punched[F, H] =
      Punched(p.focusIn, that.focusOut, [X] => (_: Unit) => p.plug[X] > that.plug[X])

    def andThen[H[_]](H: Focus[**, H], h: [x] => Unit => Shuffled[G[x], H[x]]): Punched[F, H] =
      p > Punched(p.focusOut, H, h)

    def after[H[_]](H: Focus[**, H], h: [x] => Unit => Shuffled[H[x], F[x]]): Punched[H, G] =
      Punched(H, p.focusIn, h) > p

    def inFst[P, Q](g: Shuffled[P, Q]): Punched[[x] =>> F[x] ** P, [x] =>> G[x] ** Q] =
      Punched(p.focusIn.inFst[P], p.focusOut.inFst[Q], [X] => (_: Unit) => par(p.plug[X], g))

    def inFst[P]: Punched[[x] =>> F[x] ** P, [x] =>> G[x] ** P] =
      Punched(p.focusIn.inFst[P], p.focusOut.inFst[P], [X] => (_: Unit) => p.plug[X].inFst)

    def inSnd[P, Q](f: Shuffled[P, Q]): Punched[[x] =>> P ** F[x], [x] =>> Q ** G[x]] =
      Punched(p.focusIn.inSnd[P], p.focusOut.inSnd[Q], [X] => (_: Unit) => par(f, p.plug[X]))

    def inSnd[P]: Punched[[x] =>> P ** F[x], [x] =>> P ** G[x]] =
      Punched(p.focusIn.inSnd[P], p.focusOut.inSnd[P], [X] => (_: Unit) => p.plug[X].inSnd)
  }

}

object ShuffledModule {
  type With[->[_, _], **[_, _], S <: Shuffle[**]] =
    ShuffledModule[->, **] {
      val shuffle: S
    }
}