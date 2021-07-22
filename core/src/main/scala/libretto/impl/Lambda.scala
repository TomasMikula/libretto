package libretto.impl

import libretto.BiInjective

class Lambda[-⚬[_, _], |*|[_, _]](using
  inj: BiInjective[|*|],
) {

  sealed trait Expr[A] {
    import Expr._

    def map[B](f: A -⚬ B): Expr[B] =
      Mapped(this, f, new Var[B]())

    def zip[B](that: Expr[B]): Expr[A |*| B] =
      Zip(this, that)
  }

  object Expr {
    sealed trait VarDefining[A] extends Expr[A] {
      def variable: Var[A] =
        this match {
          case v: Var[A] => v
          case Mapped(_, _, v) => v
          case Prj1(Split(_, v, _)) => v
          case Prj2(Split(_, _, v)) => v
        }
    }

    class Var[A]() extends VarDefining[A] {
      def testEqual[B](that: Var[B]): Option[A =:= B] =
        if (this eq that) Some(summon[A =:= A].asInstanceOf[A =:= B])
        else None
    }

    case class Mapped[A, B](a: Expr[A], f: A -⚬ B, b: Var[B]) extends VarDefining[B]

    case class Zip[A, B](a: Expr[A], b: Expr[B]) extends Expr[A |*| B]

    case class Prj1[A, B](p: Split[A, B]) extends VarDefining[A]

    case class Prj2[A, B](p: Split[A, B]) extends VarDefining[B]

    case class Split[X, Y](p: VarDefining[X |*| Y], p1: Var[X], p2: Var[Y])

    def unzip[A, B](p: Expr[A |*| B]): (Expr[A], Expr[B]) =
      p match {
        case Zip(a, b) =>
          (a, b)
        case p: VarDefining[A |*| B] =>
          val split = Split(p, new Var[A](), new Var[B]())
          (Prj1(split), Prj2(split))
      }
  }
  import Expr._

  val shuffled = new Shuffled[-⚬, |*|]
  import shuffled.shuffle.{~⚬, Transfer, TransferOpt}
  import shuffled.{Shuffled => ≈⚬, assocLR, assocRL, fst, id, ix, lift, pure, snd, swap, xi}

  sealed trait Vars[A] {
    def lookup[B](vb: Var[B]): Option[Vars.Contains[A, B]]

    def zip[B](that: Vars[B]): Vars[A |*| B] =
      Vars.Zip(this, that)

    def toSet: Set[Var[_]] =
      this match {
        case Vars.Single(v) => Set(v)
        case Vars.Zip(a, b) => a.toSet union b.toSet
      }
  }

  object Vars {
    case class Single[A](v: Var[A]) extends Vars[A] {
      override def lookup[B](w: Var[B]): Option[Contains[A, B]] =
        v.testEqual(w).map(_.substituteCo[Contains[A, *]](Contains.Id[A]()))
    }

    case class Zip[X, Y](_1: Vars[X], _2: Vars[Y]) extends Vars[X |*| Y] {
      override def lookup[B](w: Var[B]): Option[Contains[X |*| Y, B]] =
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
    }

    /** Witnesses that `Vars[A]` contains a variable `Var[B]`. */
    sealed trait Contains[A, B]
    object Contains {
      case class Id[X]() extends Contains[X, X]
      case class Super[A, B, X](f: A ~⚬ (B |*| X), remaining: Vars[X]) extends Contains[A, B]
    }
  }

  def abs[A, B](
    f: Expr[A] => Expr[B],
  )(using
    ev: SymmetricSemigroupalCategory[-⚬, |*|],
  ): Either[Error, A -⚬ B] = {
    val a = new Var[A]()
    val b = f(a)
    abs[A, B](
      vars = Vars.Single(a),
      expr = b,
      consumed = Set.empty,
    ) match {
      case AbsRes.Exact(f, _)                => Right(f.fold)
      case AbsRes.Partial(_, _, _)           => Left(LinearityViolation.Underused(a))
      case AbsRes.Closure(_, undefined, _)   => Left(Error.Undefined(undefined.toSet))
      case AbsRes.PartialClosure(_, _, _, _) => Left(LinearityViolation.Underused(a))
      case AbsRes.Failure(e)                 => Left(e)
    }
  }

  private def abs[A, B](
    vars: Vars[A],
    expr: Expr[B],
    consumed: Set[Var[_]],
  )(using
    ev: Semigroupoid[-⚬],
  ): AbsRes[A, B] = {
    import AbsRes._

    def goPrj[Z, X](z: VarDefining[Z], s: Z ~⚬ (B |*| X), b: Var[B], x: Var[X]): AbsRes[A, B] =
      if (consumed.contains(z.variable)) {
        if (consumed.contains(b))
          Failure(LinearityViolation.overused(b))
        else
          vars.lookup(b) match {
            case None =>
              Failure(LinearityViolation.overused(z.variable))
            case Some(contains) =>
              contains match {
                case Vars.Contains.Id()           => Exact(id, consumed + b)
                case Vars.Contains.Super(f, vars) => Partial(pure(f), vars, consumed + b)
              }
          }
      } else {
        abs[A, Z](vars, z, consumed) match {
          case Exact(f, consumed) =>
            Partial(f > pure(s), Vars.Single(x), consumed + b)
          case Partial(f, vars, consumed) =>
            Partial(f > pure(~⚬.fst(s) > ~⚬.assocLR), Vars.Single(x) zip vars, consumed + b)
          case Closure(f, undefined, consumed) =>
            PartialClosure(f thenShuffle s, undefined, Vars.Single(x), consumed + b)
          case PartialClosure(f, undefined, remaining, consumed) =>
            PartialClosure(f > pure(~⚬.fst(s) > ~⚬.assocLR), undefined, Vars.Single(x) zip remaining, consumed + b)
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
                  undefined = Vars.Single(v),
                  remaining = vars,
                  consumed = consumed + v,
                )
            }
          case Some(res) =>
            res match {
              case Vars.Contains.Id()           => Exact(id, consumed + v)
              case Vars.Contains.Super(f, vars) => Partial(pure(f), vars, consumed + v)
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
                case Vars.Contains.Id()           => Exact(id, consumed + b)
                case Vars.Contains.Super(f, vars) => Partial(pure(f), vars, consumed + b)
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
      case Prj1(Split(bx, b, x)) =>
        goPrj(bx, ~⚬.Id(), b, x)
      case Prj2(Split(xb, x, b)) =>
        goPrj(xb, ~⚬.swap, b, x)
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
    }
  }

  sealed trait Error
  object Error {
    case class Undefined(vars: Set[Var[_]]) extends Error
  }

  enum LinearityViolation extends Error {
    case Overused(vars: Set[Var[_]])
    case Underused(v: Var[_])
  }

  object LinearityViolation {
    def overused(v: Var[_]): LinearityViolation.Overused =
      LinearityViolation.Overused(Set(v))
  }
}
