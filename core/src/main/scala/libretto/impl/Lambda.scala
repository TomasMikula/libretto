package libretto.impl

import libretto.BiInjective

class Lambda[-⚬[_, _], |*|[_, _]](using
  inj: BiInjective[|*|],
) {

  sealed trait Expr[+F[_], A] {
    import Expr._

    def map[B](f: A -⚬ B): Expr[F, B] =
      Mapped(this, f, new Var[B]())
  }

  object Expr {
    sealed trait VarDefining[+F[_], A] extends Expr[F, A] {
      def variable: Var[A] =
        this match {
          case v: Var[A] => v
          case Mapped(_, _, v) => v
          case Prj1(Split(_, _, v, _)) => v
          case Prj2(Split(_, _, _, v)) => v
        }
    }

    class Var[A]() extends VarDefining[Nothing, A] {
      def testEqual[B](that: Var[B]): Option[A =:= B] =
        if (this eq that) Some(summon[A =:= A].asInstanceOf[A =:= B])
        else None
    }

    object Var {
      given Unique[Var] =
        new Unique[Var] {
          override def testEqual[A, B](a: Var[A], b: Var[B]): Option[A =:= B] =
            a testEqual b
        }
    }

    case class Mapped[+F[_], A, B](a: Expr[F, A], f: A -⚬ B, b: Var[B]) extends VarDefining[F, B]

    case class Zip[+F[_], A, B](a: Expr[F, A], b: Expr[F, B]) extends Expr[F, A |*| B]

    case class Prj1[+F[_], A, B](p: Split[F, A, B]) extends VarDefining[F, A]

    case class Prj2[+F[_], A, B](p: Split[F, A, B]) extends VarDefining[F, B]

    /** Extension point. */
    case class Ext[F[_], B](expr: F[B]) extends Expr[F, B]

    case class Split[+F[_], X, Y](p: Expr[F, X |*| Y], pv: Var[X |*| Y], p1: Var[X], p2: Var[Y])

    def zip[F[_], A, B](a: Expr[F, A], b: Expr[F, B]): Expr[F, A |*| B] =
      Zip(a, b)

    def unzip[F[_], A, B](p: Expr[F, A |*| B])(resultVar: [x] => F[x] => Var[x]): (Expr[F, A], Expr[F, B]) =
      p match {
        case Zip(a, b) =>
          (a, b)
        case p: VarDefining[F, A |*| B] =>
          val split = Split(p, p.variable, new Var[A](), new Var[B]())
          (Prj1(split), Prj2(split))
        case p @ Ext(fab) =>
          val split = Split(p, resultVar(fab), new Var[A](), new Var[B]())
          (Prj1(split), Prj2(split))
      }
  }
  import Expr._

  val shuffled = new Shuffled[-⚬, |*|]
  import shuffled.shuffle.{~⚬, Transfer, TransferOpt}
  import shuffled.{Shuffled => ≈⚬, assocLR, assocRL, fst, id, ix, lift, pure, snd, swap, xi}

  sealed trait Tupled[F[_], A] {
    def lookup[B](fb: F[B])(using Unique[F]): Option[Tupled.Contains[F, A, B]]

    def compare[B](that: Tupled[F, B])(using Unique[F]): Tupled.Cmp[F, A, B]

    def zip[B](that: Tupled[F, B]): Tupled[F, A |*| B] =
      Tupled.Zip(this, that)

    def mapReduce[G[_]](
      map: [x] => F[x] => G[x],
      zip: [x, y] => (G[x], G[y]) => G[x |*| y],
    ): G[A] =
      this match {
        case Tupled.Single(a) => map(a)
        case Tupled.Zip(x, y) => zip(x.mapReduce(map, zip), y.mapReduce(map, zip))
      }

    def mapReduce0[B](
      map: [x] => F[x] => B,
      reduce: (B, B) => B,
    ): B = {
      type G[x] = B
      mapReduce[G](map, [x, y] => (x: G[x], y: G[y]) => reduce(x, y))
    }
  }

  object Tupled {
    case class Single[F[_], A](v: F[A]) extends Tupled[F, A] {
      override def lookup[B](w: F[B])(using F: Unique[F]): Option[Contains[F, A, B]] =
        F.testEqual(v, w).map(_.substituteCo[Contains[F, A, *]](Contains.Id[F, A]()))

      override def compare[B](that: Tupled[F, B])(using F: Unique[F]): Cmp[F, A, B] =
        that match {
          case Single(w) =>
            F.testEqual(v, w) match {
              case Some(ev) => Cmp.Iso(~⚬.Id0(ev))
              case None     => Cmp.Disjoint()
            }
          case other =>
            (other compare this).invert
        }
    }

    case class Zip[F[_], X, Y](_1: Tupled[F, X], _2: Tupled[F, Y]) extends Tupled[F, X |*| Y] {
      override def lookup[B](w: F[B])(using Unique[F]): Option[Contains[F, X |*| Y, B]] =
        _1.lookup(w) match {
          case Some(contains) =>
            contains match {
              case Contains.Id()                => Some(Contains.Super(~⚬.Id(), _2))
              case Contains.Super(f, remaining) => Some(Contains.Super(~⚬.fst(f) > ~⚬.assocLR, remaining zip _2))
            }
          case None =>
            _2.lookup(w) match {
              case Some(contains) =>
                contains match {
                  case Contains.Id()                => Some(Contains.Super(~⚬.swap, _1))
                  case Contains.Super(f, remaining) => Some(Contains.Super(~⚬.snd(f) > ~⚬.xi, _1 zip remaining))
                }
              case None =>
                None
            }
        }

      override def compare[B](that: Tupled[F, B])(using Unique[F]): Cmp[F, X |*| Y, B] = {
        import Cmp._

        (_1 compare that) match {
          case Disjoint() =>
            (_2 compare that) match {
              case Disjoint() => Disjoint()
              case other => ??? // TODO
            }
          case Iso(s) =>
            Superset(~⚬.fst(s), _2)
          case Superset(s, unused) =>
            Superset(~⚬.fst(s) > ~⚬.assocLR, unused zip _2)
          case Subset(missing, s) =>
            (_2 compare missing) match {
              case Disjoint() => SymDiff(missing, ~⚬.assocRL > ~⚬.fst(s), _2)
              case other => ??? // TODO
            }
          case SymDiff(missing, s, unused) =>
            (_2 compare missing) match {
              case Disjoint() => SymDiff(missing, ~⚬.assocRL > ~⚬.fst(s) > ~⚬.assocLR, unused zip _2)
              case other => ??? // TODO
            }
        }
      }
    }

    /** Witnesses that `Tupled[F, A]` contains a variable `Var[B]`. */
    sealed trait Contains[F[_], A, B]
    object Contains {
      case class Id[F[_], X]() extends Contains[F, X, X]
      case class Super[F[_], A, B, X](f: A ~⚬ (B |*| X), remaining: Tupled[F, X]) extends Contains[F, A, B]
    }

    sealed trait Cmp[F[_], A, B] {
      import Cmp._

      def invert: Cmp[F, B, A] =
        this match {
          case Disjoint()       => Disjoint()
          case Iso(s)           => Iso(s.invert)
          case Superset(s, v)   => Subset(v, ~⚬.swap > s.invert)
          case Subset(v, s)     => Superset(s.invert > ~⚬.swap, v)
          case SymDiff(v, s, w) => SymDiff(w, ~⚬.swap > s.invert > ~⚬.swap, v)
        }
    }

    object Cmp {
      case class Disjoint[F[_], A, B]() extends Cmp[F, A, B]
      case class Iso[F[_], A, B](s: A ~⚬ B) extends Cmp[F, A, B]
      case class Superset[F[_], A, B, Y](s: A ~⚬ (B |*| Y), unused: Tupled[F, Y]) extends Cmp[F, A, B]
      case class Subset[F[_], X, A, B](missing: Tupled[F, X], s: (X |*| A) ~⚬ B) extends Cmp[F, A, B]
      case class SymDiff[F[_], X, A, B, Y](missing: Tupled[F, X], s: (X |*| A) ~⚬ (B |*| Y), unused: Tupled[F, Y]) extends Cmp[F, A, B]
    }
  }

  type Vars[A] = Tupled[Var, A]
  object Vars {
    type Cmp[A, B] = Tupled.Cmp[Var, A, B]
    val Cmp = Tupled.Cmp

    def single[A](a: Var[A]): Vars[A] =
      Tupled.Single(a)

    def toSet[A](vars: Vars[A]): Set[Var[?]] =
      vars.mapReduce0(
        map    = [x] => (v: Var[x]) => Set[Var[?]](v),
        reduce = _ union _,
      )
  }

  extension [A](vars: Vars[A]) {
    def toSet: Set[Var[?]] =
      Vars.toSet(vars)
  }

  trait Abstractable[F[_]] {
    // TODO: Don't take previously consumed variables.
    // Instead, return a precise description of the variables consumed by _this_ invocation,
    // so that such descriptions can be merged.
    def abs[A, B](vars: Vars[A], expr: F[B], consumed: Set[Var[_]]): AbsRes[A, B]
  }

  object Abstractable {
    def apply[F[_]](implicit ev: Abstractable[F]): Abstractable[F] =
      ev

    implicit val abstractableUninhabited: Abstractable[Uninhabited] =
      new Abstractable[Uninhabited] {
        override def abs[A, B](vars: Vars[A], expr: Uninhabited[B], consumed: Set[Var[_]]): AbsRes[A, B] =
          expr.as[AbsRes[A, B]]
      }

    implicit def abstractableExpr[F[_]](using
      Abstractable[F],
      Semigroupoid[-⚬],
    ): Abstractable[Expr[F, *]] =
      new Abstractable[Expr[F, *]] {
        override def abs[A, B](
          vars: Vars[A],
          expr: Expr[F, B],
          consumed: Set[Var[?]],
        ): AbsRes[A, B] =
          Lambda.this.abs(vars, expr, consumed)
      }
  }

  def abs[F[_], A, B](
    f: Expr[F, A] => Expr[F, B],
  )(using
    F: Abstractable[F],
    ev: SymmetricSemigroupalCategory[-⚬, |*|],
  ): Either[Error, A -⚬ B] = {
    val a = new Var[A]()
    val b = f(a)
    abs[F, A, B](
      vars = Vars.single(a),
      expr = b,
      consumed = Set.empty,
    ) match {
      case AbsRes.Exact(f, _)                => Right(f.fold)
      case AbsRes.Partial(_, _, _)           => Left(LinearityViolation.underused(a))
      case AbsRes.Closure(_, undefined, _)   => Left(Error.Undefined(undefined.toSet))
      case AbsRes.PartialClosure(_, _, _, _) => Left(LinearityViolation.underused(a))
      case AbsRes.Failure(e)                 => Left(e)
    }
  }

  def abs[F[_], A, B](
    vars: Vars[A],
    expr: Expr[F, B],
    consumed: Set[Var[_]],
  )(using
    F: Abstractable[F],
    ev: Semigroupoid[-⚬],
  ): AbsRes[A, B] = {
    import AbsRes._

    def goPrj[Z, X](z: Expr[F, Z], vz: Var[Z], s: Z ~⚬ (B |*| X), b: Var[B], x: Var[X]): AbsRes[A, B] =
      if (consumed.contains(vz)) {
        if (consumed.contains(b))
          Failure(LinearityViolation.overused(b))
        else
          vars.lookup(b) match {
            case None =>
              Failure(LinearityViolation.overused(vz))
            case Some(contains) =>
              contains match {
                case Tupled.Contains.Id()           => Exact(id, consumed + b)
                case Tupled.Contains.Super(f, vars) => Partial(pure(f), vars, consumed + b)
              }
          }
      } else {
        abs[F, A, Z](vars, z, consumed) match {
          case Exact(f, consumed) =>
            Partial(f > pure(s), Vars.single(x), consumed + b)
          case Partial(f, vars, consumed) =>
            Partial(f > pure(~⚬.fst(s) > ~⚬.assocLR), Vars.single(x) zip vars, consumed + b)
          case Closure(f, undefined, consumed) =>
            PartialClosure(f thenShuffle s, undefined, Vars.single(x), consumed + b)
          case PartialClosure(f, undefined, remaining, consumed) =>
            PartialClosure(f > pure(~⚬.fst(s) > ~⚬.assocLR), undefined, Vars.single(x) zip remaining, consumed + b)
          case Failure(e) =>
            Failure(e)
        }
      }

    expr match {
      case v: Var[B] =>
        vars.lookup(v) match {
          case None =>
            consumed.contains(v) match {
              case true =>
                Failure(LinearityViolation.overused(v))
              case false =>
                PartialClosure(
                  id[B |*| A],
                  undefined = Vars.single(v),
                  remaining = vars,
                  consumed = consumed + v,
                )
            }
          case Some(res) =>
            res match {
              case Tupled.Contains.Id()           => Exact(id, consumed + v)
              case Tupled.Contains.Super(f, vars) => Partial(pure(f), vars, consumed + v)
            }
        }
      case Zip(b1, b2) =>
        abs(vars, b1, consumed) match {
          case Partial(f, remaining, consumed) =>
            abs(remaining, b2, consumed) match {
              case Exact(g, consumed) =>
                Exact(f > snd(g), consumed)
              case Partial(g, remaining, consumed) =>
                Partial(f > snd(g) > assocRL, remaining, consumed)
              case Closure(g, undefined, consumed) =>
                Closure(snd(f) > xi > snd(g), undefined, consumed)
              case PartialClosure(g, undefined, remaining, consumed) =>
                PartialClosure(snd(f) > xi > snd(g) > assocRL, undefined, remaining, consumed)
              case Failure(e) =>
                Failure(e)
            }
          case PartialClosure(f, undefined, remaining, consumed) =>
            abs(remaining, b2, consumed) match {
              case Exact(g, consumed) =>
                Closure(f > snd(g), undefined, consumed)
              case Closure(g, undefined1, consumed) =>
                Closure(ix > fst(f) > assocLR > snd(swap > g), undefined zip undefined1, consumed)
              case Partial(g, remaining, consumed) =>
                PartialClosure(f > snd(g)> assocRL, undefined, remaining, consumed)
              case PartialClosure(g, undefined1, remaining, consumed) =>
                PartialClosure(ix > fst(f) > assocLR > snd(swap > g) > assocRL, undefined zip undefined1, remaining, consumed)
              case Failure(e) =>
                Failure(e)
            }
          case Exact(_, consumed) =>
            // This is already an error: no vars left for b2.
            // Run with the original vars for b2 just to construct a more precise error.
            abs(vars, b2, consumed) match {
              case Exact(_, _) | Closure(_, _, _)     => Failure.overused(vars.toSet)
              case Partial(_, remaining, _)           => Failure.overused(vars.toSet diff remaining.toSet)
              case PartialClosure(_, _, remaining, _) => Failure.overused(vars.toSet diff remaining.toSet)
              case Failure(e)                         => Failure(e)
            }
          case Closure(_, _, consumed) =>
            // This is already an error: no vars left for b2.
            // Run with the original vars for b2 just to construct a more precise error.
            abs(vars, b2, consumed) match {
              case Exact(_, _) | Closure(_, _, _)     => Failure.overused(vars.toSet)
              case Partial(_, remaining, _)           => Failure.overused(vars.toSet diff remaining.toSet)
              case PartialClosure(_, _, remaining, _) => Failure.overused(vars.toSet diff remaining.toSet)
              case Failure(e)                         => Failure(e)
            }
          case Failure(e) =>
            Failure(e)
        }
      case Mapped(x, f, b) =>
        if (consumed.contains(b)) {
          Failure(LinearityViolation.overused(b))
        } else {
          vars.lookup(b) match {
            case Some(contains) =>
              contains match {
                case Tupled.Contains.Id()           => Exact(id, consumed + b)
                case Tupled.Contains.Super(f, vars) => Partial(pure(f), vars, consumed + b)
              }
            case None =>
              abs(vars, x, consumed) match {
                case Exact(g, consumed)                                => Exact(g > lift(f), consumed + b)
                case Partial(g, remaining, consumed)                   => Partial(g > fst(lift(f)), remaining, consumed + b)
                case Closure(g, undefined, consumed)                   => Closure(g > lift(f), undefined, consumed + b)
                case PartialClosure(g, undefined, remaining, consumed) => PartialClosure(g > fst(lift(f)), undefined, remaining, consumed + b)
                case Failure(e)                                        => Failure(e)
              }
          }
        }
      case Prj1(Split(bx, v, b, x)) =>
        goPrj(bx, v, ~⚬.Id(), b, x)
      case Prj2(Split(xb, v, x, b)) =>
        goPrj(xb, v, ~⚬.swap, b, x)
      case Ext(fb) =>
        F.abs(vars, fb, consumed)

    }
  }

  sealed trait AbsRes[A, B]
  object AbsRes {
    /**
     * @param consumed keeps track of _all_ variables consumed so far
     */
    case class Exact[A, B](
      f: A ≈⚬ B,
      consumed: Set[Var[_]],
    ) extends AbsRes[A, B]

    /**
     * @param remaining non-consumed subset of `A`
     * @param consumed keeps track of _all_ variables consumed so far
     */
    case class Partial[A, B, Y](
      f: A ≈⚬ (B |*| Y),
      remaining: Vars[Y],
      consumed: Set[Var[_]],
    ) extends AbsRes[A, B]

    /**
     * @param undefined variables not defined in the given context (to be captured from an outer context)
     * @param consumed keeps track of _all_ variables consumed so far
     */
    case class Closure[X, A, B](
      f: (X |*| A) ≈⚬ B,
      undefined: Vars[X],
      consumed: Set[Var[_]],
    ) extends AbsRes[A, B]

    /**
     * @param undefined variables not defined in the given context (to be captured from an outer context)
     * @param remaining non-consumed subset of `A`
     * @param consumed keeps track of _all_ variables consumed so far
     */
    case class PartialClosure[X, A, B, Y](
      f: (X |*| A) ≈⚬ (B |*| Y),
      undefined: Vars[X],
      remaining: Vars[Y],
      consumed: Set[Var[_]],
    ) extends AbsRes[A, B]

    case class Failure[A, B](e: LinearityViolation) extends AbsRes[A, B]
    object Failure {
      def overused[A, B](vars: Set[Var[_]]): Failure[A, B] =
        Failure(LinearityViolation.Overused(vars))

      def underused[A, B](vars: Set[Var[_]]): Failure[A, B] =
        Failure(LinearityViolation.Underused(vars))
    }
  }

  sealed trait Error
  object Error {
    case class Undefined(vars: Set[Var[_]]) extends Error
  }

  sealed trait LinearityViolation extends Error

  object LinearityViolation {
    case class Overused(vars: Set[Var[_]]) extends LinearityViolation {
      require(vars.nonEmpty)
    }

    case class Underused(vars: Set[Var[_]]) extends LinearityViolation {
      require(vars.nonEmpty)
    }

    def overused(v: Var[_]): LinearityViolation.Overused =
      LinearityViolation.Overused(Set(v))

    def underused(v: Var[_]): LinearityViolation.Underused =
      LinearityViolation.Underused(Set(v))
  }

  sealed trait Uninhabited[A] {
    def as[B]: B
  }

  type Expr0[A] = Expr[Uninhabited, A]

  object Expr0 {
    def zip[A, B](a: Expr0[A], b: Expr0[B]): Expr0[A |*| B] =
      Zip(a, b)

    def unzip[A, B](p: Expr0[A |*| B]): (Expr0[A], Expr0[B]) =
      Expr.unzip[Uninhabited, A, B](p)([x] => (fx: Uninhabited[x]) => fx.as[Var[x]])

    def abs[A, B](
      f: Expr0[A] => Expr0[B],
    )(using
      ev: SymmetricSemigroupalCategory[-⚬, |*|],
    ): Either[Error, A -⚬ B] =
      Lambda.this.abs[Uninhabited, A, B](f)
  }

  trait AbsTrans[G[_[_], _]] {
    def apply[F[_]: Abstractable]: Abstractable[G[F, *]]
  }

  case class ExprF[G[_[_], _], A](unfix: Expr[G[ExprF[G, *], *], A])

  object ExprF {
    def fix[G[_[_], _], A](value: Expr[G[ExprF[G, *], *], A]): ExprF[G, A] =
      ExprF(value)

    def lift[G[_[_], _], A](ga: G[ExprF[G, *], A]): ExprF[G, A] =
      fix(Ext(ga))

    def map[G[_[_], _], A, B](a: ExprF[G, A], f: A -⚬ B): ExprF[G, B] =
      fix(Mapped(a.unfix, f, new Var[B]))

    def zip[G[_[_], _], A, B](a: ExprF[G, A], b: ExprF[G, B]): ExprF[G, A |*| B] =
      fix(Zip(a.unfix, b.unfix))

    def unzip[G[_[_], _], A, B](
      ab: ExprF[G, A |*| B],
    )(
      resultVar: [x] => G[ExprF[G, *], x] => Var[x],
    ): (ExprF[G, A], ExprF[G, B]) = {
      val (a, b) = Expr.unzip(ab.unfix)(resultVar)
      (fix(a), fix(b))
    }

    implicit def abstractableExprF[G[_[_], _]](implicit
      G: AbsTrans[G],
      ev: Semigroupoid[-⚬],
    ): Abstractable[ExprF[G, *]] =
      new Abstractable[ExprF[G, *]] { self =>
        implicit val abstractableG: Abstractable[G[ExprF[G, *], *]] =
          G.apply[ExprF[G, *]](self)

        override def abs[A, B](
          vars: Vars[A],
          expr: ExprF[G, B],
          consumed: Set[Var[_]],
        ): AbsRes[A, B] =
          Lambda.this.abs[G[ExprF[G, *], *], A, B](vars, expr.unfix, consumed)
      }

    def abs[G[_[_], _], A, B](
      vars: Vars[A],
      expr: ExprF[G, B],
      consumed: Set[Var[_]],
    )(using
      G: AbsTrans[G],
      ev: SymmetricSemigroupalCategory[-⚬, |*|],
    ): AbsRes[A, B] =
      Abstractable[ExprF[G, *]].abs(vars, expr, consumed)

    def abs[G[_[_], _], A, B](
      f: ExprF[G, A] => ExprF[G, B],
    )(using
      G: AbsTrans[G],
      ev: SymmetricSemigroupalCategory[-⚬, |*|],
    ): Either[Error, A -⚬ B] = {
      implicit val abstractableG: Abstractable[G[ExprF[G, *], *]] =
        G.apply[ExprF[G, *]]

      Lambda.this.abs[G[ExprF[G, *], *], A, B](fa => f(ExprF.fix(fa)).unfix)
    }
  }
}
