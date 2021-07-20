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
  import shuffled.{Shuffled => ≈⚬, assocLR, assocRL, fst, id, lift, pure, snd, swap}

  sealed trait Vars[A] {
    def lookup[B](vb: Var[B]): Option[Vars.Contains[A, B]]

    def zip[B](that: Vars[B]): Vars[A |*| B] =
      Vars.Zip(this, that)
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
              case Contains.Id() => Some(Contains.Super(~⚬.Id(), _2))
              // TODO
            }
          case None =>
            _2.lookup(w) match {
              case Some(contains) =>
                contains match {
                  case Contains.Id() => Some(Contains.Super(~⚬.swap, _1))
                  case Contains.Super(f, remaining) => Some(Contains.Super(~⚬.Xfer(~⚬.Id(), f, Transfer.XI(TransferOpt.None())), _1 zip remaining))
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
    abs(a, b).map(_.fold)
  }

  def abs[A, B](
    a: Var[A],
    b: Expr[B],
  )(using
    ev: Semigroupoid[-⚬],
  ): Either[Error, A ≈⚬ B] =
    abs[A, B](
      vars = Vars.Single(a),
      expr = b,
      consumed = Set.empty,
    ) match {
      case AbsRes.Exact(f, _) => Right(f)
      case AbsRes.Partial(_, _, _) => Left(LinearityViolation.Underused(a))
      case AbsRes.Failure(e) => Left(e)
    }

  private def abs[A, B](
    vars: Vars[A],
    expr: Expr[B],
    consumed: Set[Var[_]],
  )(using
    ev: Semigroupoid[-⚬],
  ): AbsRes[A, B] = {
    def goPrj[Z, X](z: VarDefining[Z], s: Z ~⚬ (B |*| X), b: Var[B], x: Var[X]): AbsRes[A, B] =
      if (consumed.contains(z.variable)) {
        if (consumed.contains(b))
          AbsRes.Failure(LinearityViolation.Overused(b))
        else
          vars.lookup(b) match {
            case None =>
              AbsRes.Failure(LinearityViolation.Overused(z.variable))
            case Some(contains) =>
              contains match {
                case Vars.Contains.Id() => AbsRes.Exact(id, consumed + b)
                case Vars.Contains.Super(f, vars) => AbsRes.Partial(pure(f), vars, consumed + b)
              }
          }
      } else {
        abs(vars, z, consumed) match {
          case AbsRes.Exact(f, consumed) => AbsRes.Partial(f > pure(s), Vars.Single(x), consumed + b)
          case AbsRes.Partial(f, vars, consumed) => AbsRes.Partial(f > pure(~⚬.fst(s) > ~⚬.assocLR), Vars.Single(x) zip vars, consumed + b)
          case AbsRes.Failure(e) => AbsRes.Failure(e)
        }
      }

    expr match {
      case v: Var[B] =>
        vars.lookup(v) match {
          case None =>
            consumed.contains(v) match {
              case true =>
                AbsRes.Failure(LinearityViolation.Overused(v))
              case false =>
                AbsRes.PartialClosure(
                  id[B |*| A],
                  undefined = Vars.Single(v),
                  remaining = vars,
                  consumed = consumed + v,
                )
            }
          case Some(res) =>
            res match {
              case Vars.Contains.Id() => AbsRes.Exact(id, consumed + v)
              case Vars.Contains.Super(f, vars) => AbsRes.Partial(pure(f), vars, consumed + v)
            }
        }
      case Zip(b1, b2) =>
        abs(vars, b1, consumed) match {
          case AbsRes.Partial(f, vars, consumed) =>
            abs(vars, b2, consumed) match {
              case AbsRes.Exact(g, consumed) => AbsRes.Exact(f > snd(g), consumed)
              case AbsRes.Partial(g, vars, consumed) => AbsRes.Partial(f > snd(g) > assocRL, vars, consumed)
              case AbsRes.Failure(e) => AbsRes.Failure(e)
            }
          // TODO
        }
      case Mapped(x, f, b) =>
        if (consumed.contains(b)) {
          AbsRes.Failure(LinearityViolation.Overused(b))
        } else {
          vars.lookup(b) match {
            case Some(contains) =>
              contains match {
                case Vars.Contains.Id() => AbsRes.Exact(id, consumed + b)
                case Vars.Contains.Super(f, vars) => AbsRes.Partial(pure(f), vars, consumed + b)
              }
            case None =>
              abs(vars, x, consumed) match {
                case AbsRes.Exact(g, consumed) => AbsRes.Exact(g > lift(f), consumed + b)
                case AbsRes.Partial(g, vars, consumed) => AbsRes.Partial(g > fst(lift(f)), vars, consumed + b)
                case AbsRes.Failure(e) => AbsRes.Failure(e)
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
  }

  sealed trait Error
  object Error {
    case class Undefined(vars: Set[Var[_]]) extends Error
  }

  enum LinearityViolation extends Error {
    case Overused(v: Var[_])
    case Underused(v: Var[_])
  }
}
