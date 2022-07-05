package libretto.impl

import libretto.impl.Lambdas.Error.LinearityViolation
import libretto.impl.Lambdas.ErrorFactory
import libretto.util.BiInjective
import scala.annotation.targetName

class LambdasImpl[-⚬[_, _], |*|[_, _], Var[_], VarSet, E, LE](using
  ssc: SymmetricSemigroupalCategory[-⚬, |*|],
  inj: BiInjective[|*|],
  variables: Variable[Var, VarSet],
  errors: ErrorFactory[E, LE, VarSet],
) extends Lambdas[-⚬, |*|, Var, VarSet, E, LE] {
  import variables.testEqual

  val shuffled = new Shuffled[-⚬, |*|]
  import shuffled.shuffle.{~⚬, Transfer, TransferOpt}
  import shuffled.{Shuffled => ≈⚬, assocLR, assocRL, fst, id, ix, ixi, lift, par, pure, snd, swap, xi}

  override type AbstractFun[A, B] =
    A ≈⚬ B

  override object AbstractFun extends AbstractFuns {
    override def fold[A, B](f: AbstractFun[A, B]): A -⚬ B =
      f.fold
  }

  /**
   * Arrow interspersed with intermediate [[Var]]s.
   * Non-linear: includes projections and multiple occurrences of the same variable.
   */
  sealed trait VArr[A, B] {
    import VArr._

    def initialVars: Vars[A] =
      this match {
        case Id(a)         => Vars.single(a)
        case Map(f, _, _)  => f.initialVars
        case Zip(f, g, _)  => f.initialVars zip g.initialVars
        case Par(f, g)     => f.initialVars zip g.initialVars
        case Prj1(f, _, _) => f.initialVars
        case Prj2(f, _, _) => f.initialVars
      }

    def terminalVars: Vars[B] =
      this match {
        case vd: VarDefining[A, B] => Vars.single(vd.resultVar)
        case Par(f, g)             => Vars.zip(f.terminalVars, g.terminalVars)
      }

    def map[C](f: B -⚬ C)(resultVar: Var[C]): VArr[A, C] =
      Map(this, f, resultVar)

    def par[C, D](that: VArr[C, D]): VArr[A |*| C, B |*| D] =
      Par(this, that)

    def zip[C, D](that: VArr[C, D])(resultVar: Var[B |*| D]): VArr[A |*| C, B |*| D] =
      Zip(this, that, resultVar)

    def elimStep[V](v: Var[V]): ElimStep[V, B] =
      this match {
        case Par(f1, f2) =>
          ElimStep.ofPar(v, f1, f2)
        case thiz: VarDefining[A, B] =>
          testEqual(v, thiz.resultVar) match {
            case Some(ev) =>
              ElimStep.Exact(ev.substituteContra(thiz), shuffled.id(ev))
            case None =>
              thiz match {
                case Id(b) =>
                  ElimStep.NotFound()
                case Map(f, g, b) =>
                  f.elimStep(v).map(g)
                case Prj1(f, b1, b2) =>
                  ElimStep.halfUsed1(f.elimStep(v), b2)
                case Prj2(f, b1, b2) =>
                  ElimStep.halfUsed2(f.elimStep(v), b1)
                case Zip(f1, f2, _) =>
                  ElimStep.ofPar(v, f1, f2)
              }
          }
      }

    def elim[V](v: Var[V]): ElimRes[V, B] =
      this.elimStep(v) match {
        case ElimStep.NotFound()       => ElimRes.unused(v)
        case ElimStep.Exact(e, f)      => ElimRes.Exact(e, f)
        case ElimStep.Closure(x, e, f) => ElimRes.Closure(x, e, f)
        case ElimStep.HalfUsed(_, u)   => ElimRes.unused(u) // TODO: also report all half-used vars
        case ElimStep.Overused(u)      => ElimRes.overused(u)
      }
  }

  object VArr extends VArrs {
    sealed trait VarDefining[A, B] extends VArr[A, B] {
      def resultVar: Var[B]
    }

    case class Id[A](variable: Var[A]) extends VarDefining[A, A] {
      override def resultVar: Var[A] =
        variable
    }

    case class Map[A, B, C](
      f: VArr[A, B],
      g: B -⚬ C,
      resultVar: Var[C],
    ) extends VarDefining[A, C]

    case class Par[A1, A2, B1, B2](
      f1: VArr[A1, B1],
      f2: VArr[A2, B2],
    ) extends VArr[A1 |*| A2, B1 |*| B2]

    /** Like [[Par]], but defines a new variable to store the result */
    case class Zip[A1, A2, B1, B2](
      f1: VArr[A1, B1],
      f2: VArr[A2, B2],
      resultVar: Var[B1 |*| B2],
    ) extends VarDefining[A1 |*| A2, B1 |*| B2]

    case class Prj1[A, B1, B2](f: VArr[A, B1 |*| B2], b1: Var[B1], b2: Var[B2]) extends VarDefining[A, B1] {
      override def resultVar: Var[B1] =
        b1
    }

    case class Prj2[A, B1, B2](f: VArr[A, B1 |*| B2], b1: Var[B1], b2: Var[B2]) extends VarDefining[A, B2] {
      override def resultVar: Var[B2] =
        b2
    }

    sealed trait ElimStep[V, B] {
      import ElimStep._

      def map[C](f: B ≈⚬ C): ElimStep[V, C]

      def map[C](f: B -⚬ C): ElimStep[V, C] =
        map(shuffled.lift(f))
    }

    object ElimStep {
      case class NotFound[V, B]() extends ElimStep[V, B] {
        override def map[C](f: B ≈⚬ C): ElimStep[V, C] =
          NotFound()
      }

      case class Overused[U, V, B](u: Var[U]) extends ElimStep[V, B] {
        override def map[C](f: B ≈⚬ C): ElimStep[V, C] =
          Overused(u)
      }

      sealed trait Found[V, B] extends ElimStep[V, B] {
        def foundVar: Var[V] =
          this match {
            case Exact(e, _)      => e.resultVar
            case Closure(_, e, _) => e.resultVar
            case HalfUsed(f, _)   => f.foundVar
          }

        override def map[C](f: B ≈⚬ C): Found[V, C] =
          this match {
            case Exact(e, g)      => Exact(e, g > f)
            case Closure(x, e, g) => Closure(x, e, g > f)
            case HalfUsed(g, u)   => HalfUsed(g map fst(f), u)
          }

        /** Along the way tries to resolve captured vars of `expr` to unused variables of `this`. */
        def withExpr[X](expr: Expr[X]): ElimStep[V, X |*| B] =
          this match {
            case Exact(e, f) =>
              expr.elimStep(e.resultVar) match {
                case NotFound() => Closure(expr, e, snd(f))
                case other => UnhandledCase.raise(s"$other")
              }
            case HalfUsed(f, u) =>
              expr.elimStep(u) match {
                case NotFound()               => halfUsed1(f.withExpr(expr).map(assocRL), u)
                case Exact(_, h)              => f.map(snd(h) > swap)
                case Closure(captured1, _, h) => f.withExpr(captured1).map(snd(swap) > assocRL > fst(h))
                case HalfUsed(g, w)           => halfUsed1(ElimStep.thenSnd(f, g) map (assocRL > fst(swap)), w)
                case Overused(w)              => Overused(w)
              }
            case Closure(captured, e, f) =>
              expr.elimStep(e.resultVar) match {
                case NotFound() => Closure(expr par captured, e, assocLR > snd(f))
                case other      => UnhandledCase.raise(s"$other")
              }
          }

        /** Assumes `captured` does not contain [[foundVar]] (and thus neither any vars derived from it).
         *  Since `captured` uses only external variables, a closure will be created.
         */
        def withCaptured[X](captured: Expr[X]): Found[V, X |*| B] =
          this match {
            case Exact(e, f) =>
              Closure(captured, e, snd(f))
            case HalfUsed(f, u) =>
              HalfUsed(f.withCaptured(captured).map(assocRL), u)
            case Closure(y, e, f) =>
              Closure(captured par y, e, assocLR > snd(f))
          }
      }

      case class Exact[V, B](expr: Expr.VarDefining[V], f: V ≈⚬ B) extends Found[V, B]
      case class Closure[X, V, B](captured: Expr[X], expr: Expr.VarDefining[V], f: (X |*| V) ≈⚬ B) extends Found[V, B]
      case class HalfUsed[V, B, U](f: Found[V, B |*| U], unused: Var[U]) extends Found[V, B]

      def overused[U, V, B](u: Var[U]): ElimStep[V, B] =
        Overused(u)

      def halfUsed1[V, B, U](step: ElimStep[V, B |*| U], u: Var[U]): ElimStep[V, B] =
        step match {
          case NotFound()               => NotFound()
          case Overused(w)              => Overused(w)
          case found: Found[V, B |*| U] => HalfUsed(found, u)
        }

      def halfUsed2[V, U, B](step: ElimStep[V, U |*| B], u: Var[U]): ElimStep[V, B] =
        halfUsed1(step.map(swap[U, B]), u)

      def closure[X, V, W, B](captured: Expr[X], f: Found[V, W], g: (X |*| W) ≈⚬ B): ElimStep[V, B] =
        f.withExpr(captured).map(g)

      def ofPar[V, B1, B2](
        v: Var[V],
        f1: Expr[B1],
        f2: Expr[B2],
      ): ElimStep[V, B1 |*| B2] =
        f1.elimStep(v) match {
          case ElimStep.NotFound() =>
            f2.elimStep(v) match {
              case ElimStep.NotFound() =>
                ElimStep.NotFound()
              case ElimStep.Exact(e2, g2) =>
                ElimStep.Closure(f1, e2, snd(g2))
              case ElimStep.Closure(x, e2, g2) =>
                ElimStep.Closure(f1 par x, e2, assocLR > snd(g2))
              case ElimStep.HalfUsed(f2, u) =>
                ElimStep.HalfUsed(f2.withCaptured(f1).map(assocRL), u)
              case ElimStep.Overused(w) =>
                ElimStep.Overused(w)
            }
          case ElimStep.Exact(e1, g1) =>
            f2.elimStep(v) match {
              case ElimStep.NotFound() =>
                ElimStep.Closure(f2, e1, snd(g1) > swap)
              case found: Found[V, B2] =>
                ElimStep.overused(v)
              case ElimStep.Overused(w) =>
                ElimStep.Overused(w)
            }
          case ElimStep.Closure(captured, e, f) =>
            f2.elimStep(v) match {
              case ElimStep.NotFound() =>
                ElimStep.Closure(f2 par captured, e, assocLR > snd(f) > swap)
              case other =>
                UnhandledCase.raise(s"$other")
            }
          case ElimStep.HalfUsed(h1, u) =>
            f2.elimStep(u) match {
              case ElimStep.NotFound() =>
                halfUsed1(h1.withExpr(f2).map(assocRL > fst(swap)), u)
              case ElimStep.Exact(g2, h2) =>
                h1 map snd(h2)
              case ElimStep.Closure(captured, g2, h2) =>
                h1.withExpr(captured).map(xi > snd(h2))
              case ElimStep.HalfUsed(g2, w) =>
                ElimStep.halfUsed1(ElimStep.thenSnd(h1, g2).map(assocRL), w)
              case ElimStep.Overused(w) =>
                ElimStep.Overused(w)
            }
          case ElimStep.Overused(w) =>
            ElimStep.Overused(w)
        }

      def thenSnd[V, B1, X, B2](f: Found[V, B1 |*| X], g: Found[X, B2]): ElimStep[V, B1 |*| B2] =
        g match {
          case Exact(g0, g1)   => f.map(snd(g1))
          case HalfUsed(g0, u) => halfUsed1(thenSnd(f, g0).map(assocRL), u)
          case Closure(captured, g, h) => f.withExpr(captured).map(xi > snd(h))
        }
    }

    sealed trait ElimRes[V, B]
    object ElimRes {
      case class Exact[V, B](expr: Expr[V], f: V ≈⚬ B) extends ElimRes[V, B]
      case class Closure[X, V, B](captured: Expr[X], expr: Expr[V], f: (X |*| V) ≈⚬ B) extends ElimRes[V, B]
      case class Error[V, B](e: LE) extends ElimRes[V, B]

      def unused[U, V, B](u: Var[U]): ElimRes[V, B] =
        Error(errors.underusedVars(variables.singleton(u)))

      def overused[U, V, B](u: Var[U]): ElimRes[V, B] =
        Error(errors.overusedVars(variables.singleton(u)))
    }

    override def id[A](a: Var[A]): VArr[A, A] =
      VArr.Id(a)

    override def map[A, B, C](f: VArr[A, B], g: B -⚬ C, resultVar: Var[C]): VArr[A, C] =
      (f map g)(resultVar)

    override def zip[A1, A2, B1, B2](f1: VArr[A1, B1], f2: VArr[A2, B2], resultVar: Var[B1 |*| B2]): VArr[A1 |*| A2, B1 |*| B2] =
      (f1 zip f2)(resultVar)

    override def par[A1, A2, B1, B2](f1: VArr[A1, B1], f2: VArr[A2, B2]): VArr[A1 |*| A2, B1 |*| B2] =
      f1 par f2

    override def unzip[A, B1, B2](f: VArr[A, B1 |*| B2])(resultVar1: Var[B1], resultVar2: Var[B2]): (VArr[A, B1], VArr[A, B2]) =
      (Prj1(f, resultVar1, resultVar2), Prj2(f, resultVar1, resultVar2))

    override def initialVars[A, B](f: VArr[A, B]): Vars[A] =
      f.initialVars

    override def terminalVars[A, B](f: VArr[A, B]): Vars[B] =
      f.terminalVars

    override def toExpr[A, B](f: VArr[A, B]): Expr[B] =
      f
  }

  type Expr[A] = VArr[?, A]

  object Expr extends Exprs {
    type VarDefining[A] = VArr.VarDefining[?, A]

    override def variable[A](a: Var[A]): Expr[A] =
      VArr.id(a)

    override def map[A, B](e: Expr[A], f: A -⚬ B, resultVar: Var[B]): Expr[B] =
      VArr.map(e, f, resultVar)

    override def zip[A, B](a: Expr[A], b: Expr[B], resultVar: Var[A |*| B]): Expr[A |*| B] =
      VArr.zip(a, b, resultVar)

    override def par[A, B](a: Expr[A], b: Expr[B]): Expr[A |*| B] =
      VArr.par(a, b)

    override def unzip[A, B](p: Expr[A |*| B])(resultVar1: Var[A], resultVar2: Var[B]): (Expr[A], Expr[B]) =
      VArr.unzip(p)(resultVar1, resultVar2)

    override def terminalVars[A](a: Expr[A]): Vars[A] =
      VArr.terminalVars(a)
  }

  override def abs[A, B](expr: Expr[B], boundVar: Var[A]): Abstracted[A, B] = {
    import VArr.ElimRes

    expr.elim(boundVar) match {
      case ElimRes.Exact(e, f) =>
        e match {
          case VArr.Id(`boundVar`) => Lambdas.Abstracted.Exact(f)
          case other               => bug(s"Expected ${Expr.variable(boundVar)}, got $other")
        }
      case ElimRes.Closure(captured, e, f) =>
        e match {
          case VArr.Id(`boundVar`) => Lambdas.Abstracted.Closure(captured, f)
          case other               => bug(s"Expected ${Expr.variable(boundVar)}, got $other")
        }
      case ElimRes.Error(e) =>
        Lambdas.Abstracted.Failure(e)
    }
  }

  override def compile[A, B](expr: Expr[B], boundVar: Var[A]): Either[E, A -⚬ B] = {
    import Lambdas.Abstracted._

    abs(expr, boundVar) match {
      case Exact(f)             => Right(f.fold)
      case Closure(captured, _) => Left(errors.undefinedVars(captured.initialVars.toSet))
      case Failure(e)           => Left(errors.fromLinearityViolation(e))
    }
  }

  private def overusedVar[A](v: Var[A]): LinearityViolation.Overused[VarSet] =
    LinearityViolation.Overused(variables.singleton(v))

  private def underusedVar[A](v: Var[A]): LinearityViolation.Underused[VarSet] =
    LinearityViolation.Underused(variables.singleton(v))

  private def bug(msg: String): Nothing =
    throw new AssertionError(msg)
}