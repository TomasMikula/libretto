package libretto.lambda

import libretto.lambda.Lambdas.Error.LinearityViolation
import libretto.lambda.Lambdas.ErrorFactory
import libretto.util.BiInjective
import scala.annotation.{tailrec, targetName}

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
          case Found(arr, u) => Found(arr > HybridArrow.map(u, g, resultVar), Untag.Variable())
      case VArr.Par(f1, f2) =>
        ???
        // (eliminate(v, f1), eliminate(v, f2)) match
        //   case (NotFound(), NotFound())       => NotFound()
        //   case (NotFound(), Found(arr, u))    => Found(arr.alsoFst(f1), Untag.Par(Untag.Capture(), u))
        //   case (Found(arr, u), NotFound())    => Found(arr.alsoSnd(f2), Untag.Par(u, Untag.Capture()))
        //   case (Found(ar1, t), Found(ar2, u)) => Found(ar1 interweave ar2, Untag.Par(t, u))
      case VArr.Zip(f1, f2, resultVar) =>
        (eliminate(v, f1), eliminate(v, f2)) match
          case (NotFound(), NotFound())       => NotFound()
          case (NotFound(), Found(arr, u))    => Found(arr > HybridArrow.captureFst(f1, u, resultVar), Untag.Variable())
          case (Found(arr, u), NotFound())    => Found(arr > HybridArrow.captureSnd(u, f2, resultVar), Untag.Variable())
          case (Found(ar1, t), Found(ar2, u)) => Found((ar1 interweave ar2) > HybridArrow.zip(t, u, resultVar), Untag.Variable())
      case VArr.Prj1(f, b1, b2) =>
        eliminate(v, f) match
          case NotFound()    => NotFound()
          case Found(arr, u) => Found(arr > HybridArrow.prj1(u, b1, b2), Untag.Variable())
      case VArr.Prj2(f, b1, b2) =>
        eliminate(v, f) match
          case NotFound()    => NotFound()
          case Found(arr, u) => Found(arr > HybridArrow.prj2(u, b1, b2), Untag.Variable())
  }

  private enum EliminateRes[A, B] {
    case Found[A, X, B](arr: HybridArrow[A, X], u: Untag[X, B]) extends EliminateRes[A, B]
    case NotFound()
  }

  private case class HybridArrow[A, B](v: Var[A], tail: HybridArrow.Tail[Var[A], B]) {
    import HybridArrow._

    def >[C](that: Tail[B, C]): HybridArrow[A, C] =
      HybridArrow(v, tail > that)

    def to[C](ev: B =:= C): HybridArrow[A, C] =
      ev.substituteCo(this)

    def interweave[C](that: HybridArrow[A, C]): HybridArrow[A, B |*| C] = {
      assert(testEqual(this.v, that.v).isDefined)
      HybridArrow(v, HybridArrow.dupVar[A] > tail.inFst)
        .weaveIn(that.tail.inSnd)
    }

    @tailrec
    private def weaveIn[C](that: Tail[B, C]): HybridArrow[A, C] = {
      import shOp.UnconsSomeRes.{Cons, Pure}

      that.unconsSome match
        case Pure(s) =>
          HybridArrow(v, tail thenShuffle s)
        case Cons(pre, i, f, post) =>
          HybridArrow(v, tail thenShuffle pre)
            .weaveInOp(i, f)
            .weaveIn(post)
    }

    private def weaveInOp[F[_], X, Y](i: Focus[|*|, F], f: Op[X, Y])(using ev: B =:= F[X]): HybridArrow[A, F[Y]] =
      pullOut(i, f) match {
        case Some(HybridArrow(v, t)) =>
          val t1 = discardFst(t, i)
          HybridArrow(v, t1)
        case None =>
          HybridArrow(v, tail.to[F[X]] > shOp.lift(f).at(i))
      }

    private def pullOut[F[_], X, Y](i: Focus[|*|, F], op: Op[X, Y])(using ev: B =:= F[X]): Option[HybridArrow[A, F[X |*| Y]]] =
      HybridArrow.pullOut(tail.to[F[X]], i, op)
        .map(HybridArrow(v, _))

    def extractLinear[B1](u: Untag[B, B1]): HybridArrow.LinearRes[A, B1] =
      ???
  }

  private object HybridArrow {
    sealed trait Op[A, B] {
      import Op._

      def project[C](p: Projection[|*|, B, C]): shOp.ProjectRes[A, C] =
        p match {
          case Projection.Id() =>
            shOp.ProjectRes.Projected(Projection.id, shOp.lift(this))
          case p: Projection.DiscardFst[pair, b1, b2, c] =>
            this.projectSnd[b1, b2].project(p.p2, Op.project)
          case p: Projection.DiscardSnd[pair, b1, b2, c] =>
            this.projectFst[b1, b2].project(p.p1, Op.project)
          case Projection.Fst(p1) =>
            bug(s"Did not realize that the first output of $this can be projected from")
          case Projection.Snd(p2) =>
            bug(s"Did not realize that the second output of $this can be projected from")
          case Projection.Both(p1, p2) =>
            bug(s"Did not realize that both outputs of $this can be projected from")
        }

      private def projectFst[B1, B2](using ev: B =:= (B1 |*| B2)): Tail[A, B1] =
        this match {
          case u: Unzip[a, a1, a2] =>
            val BiInjective[|*|](va1_b1, _) = summon[(Var[a1] |*| Var[a2]) =:= B] andThen ev
            shOp.lift(Prj1[a, a1, a2](u.u, u.resultVar1, u.resultVar2)).to[B1](using va1_b1)
          case op: DupVar[a] =>
            val BiInjective[|*|](va_b1, _) = summon[(Var[a] |*| Var[a]) =:= B] andThen ev
            shOp.id.to[B1](using va_b1)
          case other =>
            bug(s"Did not realize that $other can be projected from")
        }

      private def projectSnd[B1, B2](using ev: B =:= (B1 |*| B2)): Tail[A, B2] =
        this match {
          case u: Unzip[a, a1, a2] =>
            val BiInjective[|*|](_, va2_b2) = summon[(Var[a1] |*| Var[a2]) =:= B] andThen ev
            shOp.lift(Prj2[a, a1, a2](u.u, u.resultVar1, u.resultVar2)).to[B2](using va2_b2)
          case op: DupVar[a] =>
            val BiInjective[|*|](_, va_b2) = summon[(Var[a] |*| Var[a]) =:= B] andThen ev
            shOp.id.to[B2](using va_b2)
          case other =>
            bug(s"Did not realize that $other can be projected from")
        }
    }
    object Op {
      case class Zip[A1, A2, B1, B2](u1: Untag[A1, B1], u2: Untag[A2, B2], resultVar: Var[B1 |*| B2]) extends Op[A1 |*| A2, Var[B1 |*| B2]]

      sealed trait SingleSource[A, B] extends Op[A, B] {
        import shOp.shuffle.{zip => zipEq}

        def gcd[C](that: SingleSource[A, C]): Option[Tail[A, B |*| C]] =
          (this, that) match {
            case (p: Prj2[a, b1, b2], q: Prj1[a_, c1, c2]) =>
              (testEqual(p.unusedVar, q.resultVar), testEqual(p.resultVar, q.unusedVar)) match
                case (Some(ev1), Some(ev2)) =>
                  Some(shOp.lift(Unzip(p.u, p.unusedVar, p.resultVar)) > shOp.swap[Var[b1], Var[b2]].to(using ev1.liftCo[[t] =>> B |*| Var[t]]))
                case (None, None) =>
                  None
                case (Some(_), None) =>
                  bug(s"Variable ${p.unusedVar} appeared as a result of two different projections")
                case (None, Some(_)) =>
                  bug(s"Variable ${p.resultVar} appeared as a result of two different projections")
            case (p: Prj2[a, b1, b2], q: Unzip[a_, c1, c2]) =>
              (testEqual(p.unusedVar, q.resultVar1), testEqual(p.resultVar, q.resultVar2)) match
                case (Some(ev1), Some(ev2)) =>
                  Some(shOp.lift(q) > shOp.snd(shOp.lift(DupVar())) > shOp.xi > shOp.fst(shOp.id(ev2.flip.liftCo[Var])))
                case (None, None) =>
                  None
                case (Some(_), None) =>
                  bug(s"Variable ${p.unusedVar} appeared as a result of two different projections")
                case (None, Some(_)) =>
                  bug(s"Variable ${p.resultVar} appeared as a result of two different projections")
            case _ =>
              UnhandledCase.raise(s"gcd($this, $that)")
          }

        def deriveContradiction[A1, A2](using ev: A =:= (A1 |*| A2)): Nothing =
          throw new AssertionError() // TODO: derive contradiction more precisely
      }
      case class Map[A, A0, B](u: Untag[A, A0], f: A0 -⚬ B, resultVar: Var[B]) extends SingleSource[A, Var[B]]
      case class Prj1[A, A1, A2](u: Untag[A, A1 |*| A2], resultVar: Var[A1], unusedVar: Var[A2]) extends SingleSource[A, Var[A1]]
      case class Prj2[A, A1, A2](u: Untag[A, A1 |*| A2], unusedVar: Var[A1], resultVar: Var[A2]) extends SingleSource[A, Var[A2]]
      case class Unzip[A, A1, A2](u: Untag[A, A1 |*| A2], resultVar1: Var[A1], resultVar2: Var[A2]) extends SingleSource[A, Var[A1] |*| Var[A2]]

      case class DupVar[A]() extends Op[Var[A], Var[A] |*| Var[A]]
      case class CaptureFst[A, A0, X](x: Expr[X], u: Untag[A, A0], resultVar: Var[X |*| A0]) extends Op[A, Var[X |*| A0]]
      case class CaptureSnd[A, A0, X](u: Untag[A, A0], x: Expr[X], resultVar: Var[A0 |*| X]) extends Op[A, Var[A0 |*| X]]
      // case class DiscardFst[A1, A2]() extends Op[A1 |*| A2, A2]

      val project: [t, u, v] => (op: Op[t, u], p: Projection[|*|, u, v]) => shOp.ProjectRes[t, v] =
        [t, u, v] => (op: Op[t, u], p: Projection[|*|, u, v]) => op.project(p)
    }

    val shOp = new Shuffled[Op, |*|]
    import shOp.shuffle.{zip => zipEq}

    type Tail[A, B] =
      shOp.Shuffled[A, B]

    def id[A](v: Var[A]): HybridArrow[A, Var[A]] =
      HybridArrow(v, shOp.id)

    def dupVar[A]: Tail[Var[A], Var[A] |*| Var[A]] =
      shOp.lift(Op.DupVar())

    def map[A, A0, B](u: Untag[A, A0], f: A0 -⚬ B, resultVar: Var[B]): Tail[A, Var[B]] =
      shOp.lift(Op.Map(u, f, resultVar))

    def captureFst[A, A0, X](x: Expr[X], u: Untag[A, A0], resultVar: Var[X |*| A0]): Tail[A, Var[X |*| A0]] =
      shOp.lift(Op.CaptureFst(x, u, resultVar))

    def captureSnd[A, A0, X](u: Untag[A, A0], x: Expr[X], resultVar: Var[A0 |*| X]): Tail[A, Var[A0 |*| X]] =
      shOp.lift(Op.CaptureSnd(u, x, resultVar))

    def zip[A1, A2, B1, B2](u1: Untag[A1, B1], u2: Untag[A2, B2], resultVar: Var[B1 |*| B2]): Tail[A1 |*| A2, Var[B1 |*| B2]] =
      shOp.lift(Op.Zip(u1, u2, resultVar))

    // def unzip[A, A1, A2](u: Untag[A, A1 |*| A2], resultVar1: Var[A1], resultVar2: Var[A2]): Tail[A, Var[A1] |*| Var[A2]] =
    //   shOp.lift(Op.Unzip(u, resultVar1, resultVar2))

    def prj1[A, A1, A2](u: Untag[A, A1 |*| A2], resultVar: Var[A1], unusedVar: Var[A2]): Tail[A, Var[A1]] =
      shOp.lift(Op.Prj1(u, resultVar, unusedVar))

    def prj2[A, A1, A2](u: Untag[A, A1 |*| A2], unusedVar: Var[A1], resultVar: Var[A2]): Tail[A, Var[A2]] =
      shOp.lift(Op.Prj2(u, unusedVar, resultVar))

    /** If `op` introduces a new variable(s), searches through `t` for an existing occurrence of `op`
     *  and channels it to the output.
     *  If `op` does not introduce new variables, or if `op` is not found in `t`, returns `None`.
     */
    def pullOut[A, G[_], X, Y](t: Tail[A, G[X]], i: Focus[|*|, G], op: Op[X, Y]): Option[Tail[A, G[X |*| Y]]] = {
      import shOp.ChaseBwRes

      op match {
        case op: Op.SingleSource[X, Y] =>
          t.chaseBw(i) match {
            case ChaseBwRes.Transported(_, _, _) =>
              None
            case r: ChaseBwRes.OriginatesFrom[a, f, v, w, x, g] =>
              pullBump(r.pre, r.i, r.f, r.w, r.post, op)
                .map(_ > shOp.absorbSnd(i))
            case ChaseBwRes.Split(ev) =>
              // TODO: prove impossible
              bug(s"Did not expect $op to originate from a pair of expressions. Expected a single variable.")
          }
        case Op.DupVar() =>
          None
        case Op.CaptureFst(x, u, resultVar) =>
          UnhandledCase.raise(s"t = $t; i = $i; op = $op")
        case Op.CaptureSnd(u, x, resultVar) =>
          UnhandledCase.raise(s"t = $t; i = $i; op = $op")
        case Op.Zip(u1, u2, resultVar) =>
          UnhandledCase.raise(s"t = $t; i = $i; op = $op")
        // case Op.DiscardFst() =>
        //   UnhandledCase.raise(s"t = $t; i = $i; op = $op")
      }
    }

    def pullBump[A, F[_], V, WX, W[_], X, G[_], Y](
      pre: Tail[A, F[V]],
      i: Focus[|*|, F],
      obstacle: Op[V, WX],
      w: Focus[|*|, W],
      post: Tail[F[W[X]], G[X]],
      op: Op.SingleSource[X, Y],
    )(using
      ev: WX =:= W[X],
    ): Option[Tail[A, G[X] |*| Y]] = {
      obstacle match
        case o: Op.DupVar[v0] =>
          summon[V =:= Var[v0]]
          summon[WX =:= (Var[v0] |*| Var[v0])]
          w match
            case w: Focus.Fst[pair, w1, q] =>
              val BiInjective[|*|](w1xvv0, qvv0) = summon[(w1[X] |*| q) =:= W[X]] andThen ev.flip andThen summon[WX =:= (Var[v0] |*| Var[v0])]
              w.i match
                case Focus.Id() =>
                  val xvv0: X =:= Var[v0] = summon[X =:= w1[X]] andThen w1xvv0
                  val vv0vv0_wx: (Var[v0] |*| Var[v0]) =:= W[X] = summon[(Var[v0] |*| Var[v0]) =:= WX] andThen ev
                  val xxwx: (X |*| X) =:= W[X] = (xvv0 zipEq xvv0) andThen vv0vv0_wx
                  pushOut[[x] =>> F[X |*| x], X, Y, G[X]](post.from(using xxwx.liftCo[F]), i compose Focus.snd[|*|, X], op) match
                    case Some(post1) =>
                      ???
                    case None =>
                      pullOut[A, F, X, Y](pre.to[F[X]](using xvv0.flip.liftCo[F]), i, op) match
                        case Some(pre1) =>
                          val post1: Tail[F[X], G[X]] = (shOp.id(xvv0) > shOp.lift(Op.DupVar[v0]()).to(using vv0vv0_wx)).at[F](i) > post
                          Some(pre1 > shOp.extractSnd[F, X, Y](i) > post1.inFst)
                        case None =>
                          ???
                case Focus.Fst(_) =>
                  throw new AssertionError() // TODO: derive contradiction
                case Focus.Snd(_) =>
                  throw new AssertionError() // TODO: derive contradiction
            case w: Focus.Snd[pair, w2, p] =>
              val BiInjective[|*|](pvv0, w2xvv0) = summon[(p |*| w2[X]) =:= W[X]] andThen ev.flip andThen summon[WX =:= (Var[v0] |*| Var[v0])]
              w.i match
                case Focus.Id() =>
                  val xvv0: X =:= Var[v0] = summon[X =:= w2[X]] andThen w2xvv0
                  val xxwx: (X |*| X) =:= W[X] = (xvv0 zipEq xvv0) andThen summon[(Var[v0] |*| Var[v0]) =:= WX] andThen ev
                  pushOut[[x] =>> F[x |*| X], X, Y, G[X]](post.from(using xxwx.liftCo[F]), i compose Focus.fst[|*|, X], op) match
                    case Some(post1) =>
                      Some(pre > shOp.lift(Op.DupVar[v0]()).to[X |*| X](using (xvv0 zipEq xvv0).flip).at[F](i) > post1)
                    case None =>
                      ???
                case Focus.Fst(_) =>
                  throw new AssertionError() // TODO: derive contradiction
                case Focus.Snd(_) =>
                  throw new AssertionError() // TODO: derive contradiction
            case Focus.Id() =>
              val contraEv: X =:= (Var[v0] |*| Var[v0]) = summon[X =:= W[X]] andThen ev.flip andThen summon[WX =:= (Var[v0] |*| Var[v0])]
              op.deriveContradiction(using contraEv)
        case Op.Zip(u1, u2, resultVar) =>
          UnhandledCase.raise(s"$obstacle at $w followed by $op")
        case Op.CaptureFst(x, u, resultVar) =>
          UnhandledCase.raise(s"$obstacle at $w followed by $op")
        case Op.CaptureSnd(u, x, resultVar) =>
          UnhandledCase.raise(s"$obstacle at $w followed by $op")
        case Op.Unzip(u, resultVar1, resultVar2) =>
          UnhandledCase.raise(s"$obstacle at $w followed by $op")
        // case Op.DiscardFst() =>
        //   UnhandledCase.raise(s"$obstacle at $w followed by $op")
        case Op.Map(u, f, resultVar) =>
          UnhandledCase.raise(s"$obstacle at $w followed by $op")
        case Op.Prj1(u, resultVar, unusedVar) =>
          UnhandledCase.raise(s"$obstacle at $w followed by $op")
        case Op.Prj2(u, unusedVar, resultVar) =>
          UnhandledCase.raise(s"$obstacle at $w followed by $op")
    }

    def pushOut[F[_], X, Y, B](t: Tail[F[X], B], i: Focus[|*|, F], op: Op[X, Y]): Option[Tail[F[X], B |*| Y]] =
      op match {
        case op: Op.SingleSource[X, Y] =>
          t.chaseFw(i) match {
            case r: shOp.ChaseFwRes.FedTo[f, x, v, w, g, b] =>
              pushBump(r.pre, r.v, r.f, r.g, r.post, op)
            case shOp.ChaseFwRes.Transported(_, _, _) =>
              None
            case shOp.ChaseFwRes.Split(_) =>
              bug(s"Unexpected pair of expressions fed to $op")
          }
        case other =>
          UnhandledCase.raise(s"Pushing out $op from $t at $i")
      }

    def pushBump[F[_], X, V[_], W, G[_], B, Y](
      pre: Tail[F[X], G[V[X]]],
      v: Focus[|*|, V],
      obstacle: Op[V[X], W],
      g: Focus[|*|, G],
      post: Tail[G[W], B],
      op: Op.SingleSource[X, Y],
    ): Option[Tail[F[X], B |*| Y]] =
      v match {
        case Focus.Id() =>
          summon[X =:= V[X]]
          obstacle match
            case ob: Op.SingleSource[x, W] =>
              summon[x =:= X]
              (ob gcd op) map { (f: Tail[X, W |*| Y]) =>
                pre > f.at(g) > shOp.extractSnd[G, W, Y](g) > post.inFst[Y]
              }
            case Op.Zip(_, _, _) =>
              UnhandledCase.raise(s"$op hit obstacle $obstacle at $v")
            case Op.DupVar() =>
              UnhandledCase.raise(s"$op hit obstacle $obstacle at $v")
            case other =>
              UnhandledCase.raise(s"$op hit obstacle $obstacle at $v")
        case Focus.Fst(v1) =>
          UnhandledCase.raise(s"$op hit obstacle $obstacle at $v")
        case Focus.Snd(v2) =>
          UnhandledCase.raise(s"$op hit obstacle $obstacle at $v")
      }

    def discardFst[A, G[_], X, Y](t: Tail[Var[A], G[X |*| Y]], g: Focus[|*|, G]): Tail[Var[A], G[Y]] = {
      val prj: Projection[|*|, G[X |*| Y], G[Y]] = Projection.discardFst[|*|, X, Y].at[G](g)
      t.project(prj, Op.project) match
        case shOp.ProjectRes.Projected(p, f) =>
          p match
            case Projection.Id() =>
              f
            case _: Projection.Proper[pair, p, q] =>
              throw AssertionError("Cannot project from Var[A]") // TODO: derive contradiction

      // type GY[T] = G[T |*| Y]
      // t.chaseBw[GY, X](g compose Focus.fst) match
      //   case s: shOp.ChaseBwRes.Split[a, gy, x, x1, x2] =>
      //     val t1: Tail[A, G[x1 |*| (x2 |*| Y)]] = t.to[G[(x1 |*| x2) |*| Y]](using s.ev.liftCo[[t] =>> G[t |*| Y]]) > shOp.assocLR[x1, x2, Y].at(g)
      //     discardFst[A, G, x1, x2 |*| Y](t1, g) flatMap { t2 =>
      //       discardFst(t2, g)
      //     }
      //   case tr: shOp.ChaseBwRes.Transported[a, f, gy, x] =>
      //     None
      //   case r: shOp.ChaseBwRes.OriginatesFrom[a, f, v, w, x, gy] =>
      //     UnhandledCase.raise(s"${r.f} at ${r.w}")
    }

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