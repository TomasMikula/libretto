package libretto.lambda

import libretto.lambda.Lambdas.Error.LinearityViolation
import libretto.lambda.Lambdas.ErrorFactory
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
              ElimStep.Exact(ev.substituteContra(thiz), Multiplier.id, shuffled.id(ev))
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
        case ElimStep.NotFound()          => ElimRes.NotFound()
        case ElimStep.Exact(e, m, f)      => ElimRes.Exact(e, m, f)
        case ElimStep.Closure(x, e, m, f) => ElimRes.Closure(x, e, m, f)
        case ElimStep.HalfUsed(_, u)      => ElimRes.unused(u) // TODO: also report all half-used vars
        case ElimStep.Overused(u)         => ElimRes.overused(u)
      }
  }

  object VArr {
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
            case Exact(e, _, _)      => e.resultVar
            case Closure(_, e, _, _) => e.resultVar
            case HalfUsed(f, _)      => f.foundVar
          }

        override def map[C](f: B ≈⚬ C): Found[V, C] =
          this match {
            case Exact(e, m, g)      => Exact(e, m, g > f)
            case Closure(x, e, m, g) => Closure(x, e, m, g > f)
            case HalfUsed(g, u)      => HalfUsed(g map fst(f), u)
          }

        def also[V0, B0](m0: Multiplier[|*|, V, V0], f0: V0 ≈⚬ B0): Found[V, B0 |*| B] =
          this match {
            case Exact(e, m, g)      => Exact(e, Multiplier.dup(m0, m), shuffled.par(f0, g))
            case Closure(x, e, m, g) => Closure(x, e, Multiplier.dup(m0, m), xi > shuffled.par(f0, g))
            case HalfUsed(g, u)      => HalfUsed(g.also(m0, f0).map(assocRL), u)
          }

        /** Along the way tries to resolve captured vars of `expr` to unused variables of `this`. */
        def withExpr[X](expr: Expr[X]): ElimStep[V, X |*| B] =
          this match {
            case Exact(e, m, f) =>
              expr.elimStep(e.resultVar) match {
                case NotFound()       => Closure(expr, e, m, snd(f))
                case Exact(_, m0, f0) => Exact(e, Multiplier.dup(m0, m), shuffled.par(f0, f))
                case other => UnhandledCase.raise(s"$other")
              }
            case HalfUsed(f, u) =>
              expr.elimStep(u) match {
                case NotFound() =>
                  halfUsed1(f.withExpr(expr).map(assocRL), u)
                case Exact(_, m, h) =>
                  m match {
                    case Multiplier.Id() => f.map(snd(h) > swap)
                    case _               => Overused(u)
                  }
                case Closure(captured1, _, m, h) =>
                  m match {
                    case Multiplier.Id() => f.withExpr(captured1).map(snd(swap) > assocRL > fst(h))
                    case _               => Overused(u)
                  }
                case HalfUsed(g, w) =>
                  halfUsed1(ElimStep.thenSnd(f, g) map (assocRL > fst(swap)), w)
                case Overused(w) =>
                  Overused(w)
              }
            case Closure(captured, e, m, f) =>
              expr.elimStep(e.resultVar) match {
                case NotFound() => Closure(expr par captured, e, m, assocLR > snd(f))
                case other      => UnhandledCase.raise(s"$other")
              }
          }

        /** Assumes `captured` does not contain [[foundVar]] (and thus neither any vars derived from it).
         *  Since `captured` uses only external variables, a closure will be created.
         */
        def withCaptured[X](captured: Expr[X]): Found[V, X |*| B] =
          this match {
            case Exact(e, m, f) =>
              Closure(captured, e, m, snd(f))
            case HalfUsed(f, u) =>
              HalfUsed(f.withCaptured(captured).map(assocRL), u)
            case Closure(y, e, m, f) =>
              Closure(captured par y, e, m, assocLR > snd(f))
          }
      }

      case class Exact[V, V1, B](
        expr: Expr.VarDefining[V],
        m: Multiplier[|*|, V, V1],
        f: V1 ≈⚬ B,
      ) extends Found[V, B]

      case class Closure[X, V, V1, B](
        captured: Expr[X],
        expr: Expr.VarDefining[V],
        m: Multiplier[|*|, V, V1],
        f: (X |*| V1) ≈⚬ B,
      ) extends Found[V, B]

      case class HalfUsed[V, B, U](
        f: Found[V, B |*| U],
        unused: Var[U],
      ) extends Found[V, B]

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
              case ElimStep.Exact(e2, m2, g2) =>
                ElimStep.Closure(f1, e2, m2, snd(g2))
              case ElimStep.Closure(x, e2, m2, g2) =>
                ElimStep.Closure(f1 par x, e2, m2, assocLR > snd(g2))
              case ElimStep.HalfUsed(f2, u) =>
                ElimStep.HalfUsed(f2.withCaptured(f1).map(assocRL), u)
              case ElimStep.Overused(w) =>
                ElimStep.Overused(w)
            }
          case ElimStep.Exact(e1, m1, g1) =>
            f2.elimStep(v) match {
              case ElimStep.NotFound() =>
                ElimStep.Closure(f2, e1, m1, snd(g1) > swap)
              case ElimStep.Exact(e2, m2, g2) =>
                ElimStep.Exact(e1, Multiplier.dup(m1, m2), shuffled.par(g1, g2))
              case ElimStep.Closure(x2, e2, m2, g2) =>
                ElimStep.Closure(x2, e1, Multiplier.dup(m1, m2), xi > shuffled.par(g1, g2))
              case ElimStep.HalfUsed(f2, u) =>
                ElimStep.HalfUsed(f2.also(m1, g1).map(assocRL), u)
              case ElimStep.Overused(w) =>
                ElimStep.Overused(w)
            }
          case ElimStep.Closure(captured, e1, m1, g1) =>
            f2.elimStep(v) match {
              case ElimStep.NotFound() =>
                ElimStep.Closure(f2 par captured, e1, m1, assocLR > snd(g1) > swap)
              case other =>
                UnhandledCase.raise(s"$other")
            }
          case ElimStep.HalfUsed(h1, u) =>
            f2.elimStep(u) match {
              case ElimStep.NotFound() =>
                halfUsed1(h1.withExpr(f2).map(assocRL > fst(swap)), u)
              case ElimStep.Exact(e2, m2, h2) =>
                m2 match {
                  case Multiplier.Id() => h1 map snd(h2)
                  case _               => ElimStep.Overused(u)
                }
              case ElimStep.Closure(captured, g2, m2, h2) =>
                m2 match {
                  case Multiplier.Id() => h1.withExpr(captured).map(xi > snd(h2))
                  case _               => ElimStep.Overused(u)
                }
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
          case Exact(g0, m, g1) =>
            m match {
              case Multiplier.Id() => f.map(snd(g1))
              case _               => ElimStep.Overused(g0.resultVar)
            }
          case Closure(captured, g, m, h) =>
            m match {
              case Multiplier.Id() => f.withExpr(captured).map(xi > snd(h))
              case _               => ElimStep.Overused(g.resultVar)
            }
          case HalfUsed(g0, u) =>
            halfUsed1(thenSnd(f, g0).map(assocRL), u)
        }
    }

    sealed trait ElimRes[V, B]
    object ElimRes {
      case class Exact[V, V1, B](
        expr: Expr[V],
        m: Multiplier[|*|, V, V1],
        f: V1 ≈⚬ B,
      ) extends ElimRes[V, B]

      case class Closure[X, V, V1, B](
        captured: Expr[X],
        expr: Expr[V],
        m: Multiplier[|*|, V, V1],
        f: (X |*| V1) ≈⚬ B,
      ) extends ElimRes[V, B]

      case class NotFound[V, B]() extends ElimRes[V, B]

      case class Error[V, B](e: LE) extends ElimRes[V, B]

      def unused[U, V, B](u: Var[U]): ElimRes[V, B] =
        Error(errors.underusedVars(variables.singleton(u)))

      def overused[U, V, B](u: Var[U]): ElimRes[V, B] =
        Error(errors.overusedVars(variables.singleton(u)))
    }

    def id[A](a: Var[A]): VArr[A, A] =
      VArr.Id(a)

    def map[A, B, C](f: VArr[A, B], g: B -⚬ C, resultVar: Var[C]): VArr[A, C] =
      (f map g)(resultVar)

    def zip[A1, A2, B1, B2](f1: VArr[A1, B1], f2: VArr[A2, B2], resultVar: Var[B1 |*| B2]): VArr[A1 |*| A2, B1 |*| B2] =
      (f1 zip f2)(resultVar)

    def par[A1, A2, B1, B2](f1: VArr[A1, B1], f2: VArr[A2, B2]): VArr[A1 |*| A2, B1 |*| B2] =
      f1 par f2

    def unzip[A, B1, B2](f: VArr[A, B1 |*| B2])(resultVar1: Var[B1], resultVar2: Var[B2]): (VArr[A, B1], VArr[A, B2]) =
      (Prj1(f, resultVar1, resultVar2), Prj2(f, resultVar1, resultVar2))

    def initialVars[A, B](f: VArr[A, B]): Vars[A] =
      f.initialVars

    def terminalVars[A, B](f: VArr[A, B]): Vars[B] =
      f.terminalVars

    def toExpr[A, B](f: VArr[A, B]): Expr[B] =
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

  // override def abs[A, B](expr: Expr[B], boundVar: Var[A]): Abstracted[A, B] = {
  //   import VArr.ElimRes

  //   expr.elim(boundVar) match {
  //     case ElimRes.Exact(e, m, f) =>
  //       e match {
  //         case VArr.Id(`boundVar`) => Lambdas.Abstracted.Exact(m, f)
  //         case other               => bug(s"Expected ${Expr.variable(boundVar)}, got $other")
  //       }
  //     case ElimRes.Closure(captured, e, m, f) =>
  //       e match {
  //         case VArr.Id(`boundVar`) => Lambdas.Abstracted.Closure(captured, m, f)
  //         case other               => bug(s"Expected ${Expr.variable(boundVar)}, got $other")
  //       }
  //     case ElimRes.NotFound() =>
  //       Lambdas.Abstracted.NotFound(expr)
  //     case ElimRes.Error(e) =>
  //       Lambdas.Abstracted.Failure(e)
  //   }
  // }

  override def abs[A, B](expr: Expr[B], boundVar: Var[A]): Abstracted[A, B] = {
    import HybridArrow.LinearRes

    eliminate(boundVar, expr) match {
      case EliminateRes.Found(arr, u) =>
        arr.extractLinear(u) match {
          case LinearRes.Exact(m, f)             => Lambdas.Abstracted.Exact(m, f)
          case LinearRes.Closure(captured, m, f) => Lambdas.Abstracted.Closure(captured, m, f)
          case LinearRes.Violation(e)            => Lambdas.Abstracted.Failure(e)
        }
      case EliminateRes.NotFound() =>
        Lambdas.Abstracted.NotFound(expr)
    }
  }

  private def overusedVar[A](v: Var[A]): LinearityViolation.Overused[VarSet] =
    LinearityViolation.Overused(variables.singleton(v))

  private def underusedVar[A](v: Var[A]): LinearityViolation.Underused[VarSet] =
    LinearityViolation.Underused(variables.singleton(v))

  private def bug(msg: String): Nothing =
    throw new AssertionError(msg)

  // Note: The variable is only searched for among initial variables of the expression,
  // not in any (intermediate) results.
  private def eliminate[A, B](v: Var[A], expr: Expr[B]): EliminateRes[A, B] = {
    import EliminateRes.{Found, NotFound}

    expr match
      case VArr.Id(w) =>
        testEqual(v, w) match
          case None     => NotFound()
          case Some(ev) => Found(HybridArrow.id(v).to(ev.liftCo[Var]), Untag.Variable())
      case VArr.Map(f, g, resultVar) =>
        eliminate(v, f) match
          case NotFound() => NotFound()
          case Found(arr, u) => Found(arr.map(u, g, resultVar), Untag.Variable())
      case VArr.Par(f1, f2) =>
        (eliminate(v, f1), eliminate(v, f2)) match
          case (NotFound(), NotFound())       => NotFound()
          case (NotFound(), Found(arr, u))    => Found(arr.alsoFst(f1), Untag.Par(Untag.Capture(), u))
          case (Found(arr, u), NotFound())    => Found(arr.alsoSnd(f2), Untag.Par(u, Untag.Capture()))
          case (Found(ar1, t), Found(ar2, u)) => Found(ar1 interweave ar2, Untag.Par(t, u))
      case VArr.Zip(f1, f2, resultVar) =>
        (eliminate(v, f1), eliminate(v, f2)) match
          case (NotFound(), NotFound())       => NotFound()
          case (NotFound(), Found(arr, u))    => Found(arr.alsoFst(f1).zip(Untag.Par(Untag.Capture(), u), resultVar), Untag.Variable())
          case (Found(arr, u), NotFound())    => Found(arr.alsoSnd(f2).zip(Untag.Par(u, Untag.Capture()), resultVar), Untag.Variable())
          case (Found(ar1, t), Found(ar2, u)) => Found((ar1 interweave ar2).zip(Untag.Par(t, u), resultVar), Untag.Variable())
      case VArr.Prj1(f, b1, b2) =>
        eliminate(v, f) match
          case NotFound()    => NotFound()
          case Found(arr, u) => Found(arr.prj1(u, b1, b2), Untag.Variable())
      case VArr.Prj2(f, b1, b2) =>
        eliminate(v, f) match
          case NotFound()    => NotFound()
          case Found(arr, u) => Found(arr.prj2(u, b1, b2), Untag.Variable())
  }

  private enum EliminateRes[A, B] {
    case Found[A, X, B](arr: HybridArrow[A, X], u: Untag[X, B]) extends EliminateRes[A, B]
    case NotFound()
  }

  private case class HybridArrow[A, B](v: Var[A], tail: HybridArrow.Tail[Var[A], B]) {
    import HybridArrow._

    def map[B1, C](u: Untag[B, B1], f: B1 -⚬ C, resultVar: Var[C]): HybridArrow[A, Var[C]] =
      HybridArrow(v, tail.map(u, f, resultVar))

    def alsoFst[X](x: Expr[X]): HybridArrow[A, Expr[X] |*| B] =
      HybridArrow(v, tail.alsoFst(x))

    def alsoSnd[X](x: Expr[X]): HybridArrow[A, B |*| Expr[X]] =
      HybridArrow(v, tail.alsoSnd(x))

    def zip[B1, B2](u: Untag[B, B1 |*| B2], resultVar: Var[B1 |*| B2]): HybridArrow[A, Var[B1 |*| B2]] =
      HybridArrow(v, tail.zip(u, resultVar))

    def prj1[B1, B2](u: Untag[B, B1 |*| B2], resultVar: Var[B1], unusedVar: Var[B2]): HybridArrow[A, Var[B1]] =
      HybridArrow(v, tail.prj1(u, resultVar, unusedVar))

    def prj2[B1, B2](u: Untag[B, B1 |*| B2], unusedVar: Var[B1], resultVar: Var[B2]): HybridArrow[A, Var[B2]] =
      HybridArrow(v, tail.prj2(u, unusedVar, resultVar))

    def to[C](ev: B =:= C): HybridArrow[A, C] =
      ev.substituteCo(this)

    def interweave[C](that: HybridArrow[A, C]): HybridArrow[A, B |*| C] = {
      val f: HybridArrow[A, B |*| Var[A]] = this.newStrand
      // that match {
      //   case Id(v) =>
      //     f
      //   case Map(base, u, f, resultVar) =>
      //     ???
      //   case AlsoFst(x, f) =>
      //     ???
      //   case AlsoSnd(f, x) =>
      //     ???
      //   case Zip(f, u, resultVar) =>
      //     ???
      //   case Prj1(f, u, resultVar, unusedVar) =>
      //     ???
      //   case Prj2(f, u, unusedVar, resultVar) =>
      //     ???
      // }
      ???
    }

    private def newStrand: HybridArrow[A, B |*| Var[A]] =
      ???

    def extractLinear[B1](u: Untag[B, B1]): HybridArrow.LinearRes[A, B1] =
      ???
  }

  private object HybridArrow {
    sealed trait Tail[A, B] {
      def map[B1, C](u: Untag[B, B1], f: B1 -⚬ C, resultVar: Var[C]): Tail[A, Var[C]] =
        Tail.Map(this, u, f, resultVar)

      def alsoFst[X](x: Expr[X]): Tail[A, Expr[X] |*| B] =
        Tail.AlsoFst(x, this)

      def alsoSnd[X](x: Expr[X]): Tail[A, B |*| Expr[X]] =
        Tail.AlsoSnd(this, x)

      def zip[B1, B2](u: Untag[B, B1 |*| B2], resultVar: Var[B1 |*| B2]): Tail[A, Var[B1 |*| B2]] =
        Tail.Zip(this, u, resultVar)

      def prj1[B1, B2](u: Untag[B, B1 |*| B2], resultVar: Var[B1], unusedVar: Var[B2]): Tail[A, Var[B1]] =
        Tail.Prj1(this, u, resultVar, unusedVar)

      def prj2[B1, B2](u: Untag[B, B1 |*| B2], unusedVar: Var[B1], resultVar: Var[B2]): Tail[A, Var[B2]] =
        Tail.Prj2(this, u, unusedVar, resultVar)
    }

    object Tail {
      case class Id[A]() extends Tail[A, A]
      case class Map[A, X, Y, C](base: Tail[A, X], u: Untag[X, Y], f: Y -⚬ C, resultVar: Var[C]) extends Tail[A, Var[C]]
      case class AlsoFst[A, X, B](x: Expr[X], f: Tail[A, B]) extends Tail[A, Expr[X] |*| B]
      case class AlsoSnd[A, B, X](f: Tail[A, B], x: Expr[X]) extends Tail[A, B |*| Expr[X]]
      case class Zip[A, B, B1, B2](f: Tail[A, B], u: Untag[B, B1 |*| B2], resultVar: Var[B1 |*| B2]) extends Tail[A, Var[B1 |*| B2]]
      case class Prj1[A, B, B1, B2](f: Tail[A, B], u: Untag[B, B1 |*| B2], resultVar: Var[B1], unusedVar: Var[B2]) extends Tail[A, Var[B1]]
      case class Prj2[A, B, B1, B2](f: Tail[A, B], u: Untag[B, B1 |*| B2], unusedVar: Var[B1], resultVar: Var[B2]) extends Tail[A, Var[B2]]
    }

    def id[A](v: Var[A]): HybridArrow[A, Var[A]] =
      HybridArrow(v, Tail.Id())

    enum LinearRes[A, B] {
      case Exact[A, A1, B](m: Multiplier[|*|, A, A1], f: AbstractFun[A1, B]) extends LinearRes[A, B]
      case Closure[X, A, A1, B](captured: Expr[X], m: Multiplier[|*|, A, A1], f: AbstractFun[X |*| A1, B]) extends LinearRes[A, B]
      case Violation(e: LE)
    }
  }

  private enum Untag[A, B] {
    case Variable[A]() extends Untag[Var[A], A]
    case Capture[A]() extends Untag[Expr[A], A]
    case Par[A1, A2, B1, B2](e1: Untag[A1, B1], e2: Untag[A2, B2]) extends Untag[A1 |*| A2, B1 |*| B2]
  }
}