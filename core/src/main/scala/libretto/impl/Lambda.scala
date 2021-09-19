package libretto.impl

import libretto.BiInjective

class Lambda[-⚬[_, _], |*|[_, _], Var[_], VarSet](using
  inj: BiInjective[|*|],
  variables: Variable[Var, VarSet],
) {
  import variables.{newVar, testEqual}

  val shuffled = new Shuffled[-⚬, |*|]
  import shuffled.shuffle.{~⚬, Transfer, TransferOpt}
  import shuffled.{Shuffled => ≈⚬, assocLR, assocRL, fst, id, ix, ixi, lift, par, pure, snd, swap, xi}

  /**
   * Arrow interspersed with intermediate [[Var]]s.
   * Non-linear: includes projections and multiple occurrences of the same variable.
   */
  sealed trait VArr[A, B] {
    import VArr._

    def initialVars: Vars[A] =
      this match {
        case Id(a) => Vars.single(a)
        case other => UnhandledCase.raise(s"$other")
      }

    def map[C](f: B -⚬ C): VArr[A, C] =
      Map(this, f, newVar[C]())

    def zip[C, D](that: VArr[C, D]): VArr[A |*| C, B |*| D] =
      Zip(this, that, newVar[B |*| D]())

    def elimStep[V](v: Var[V]): ElimStep[V, B] =
      this match {
        case Par(f1, f2) =>
          ElimStep.ofPar(v, f1, f2)
        case thiz: VarDefining[A, B] =>
          testEqual(v, thiz.resultVar) match {
            case Some(ev) =>
              ElimStep.Exact(ev.substituteContra(thiz), id(ev))
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
        case ElimStep.NotFound()       => ElimRes.Unused(variables.singleton(v))
        case ElimStep.Exact(e, f)      => ElimRes.Exact(e, f)
        case ElimStep.Closure(x, e, f) => ElimRes.Closure(x, e, f)
        case ElimStep.HalfUsed(_, u)   => ElimRes.Unused(variables.singleton(u)) // TODO: also report all half-used vars
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

      sealed trait Found[V, B] extends ElimStep[V, B] {
        override def map[C](f: B ≈⚬ C): Found[V, C] =
          this match {
            case Exact(e, g)      => Exact(e, g > f)
            case Closure(x, e, g) => Closure(x, e, g > f)
            case HalfUsed(g, u)   => HalfUsed(g map fst(f), u)
            // TODO
          }

        def withCaptured[X](captured: Expr[X]): Found[V, X |*| B] =
          this match {
            case Exact(e, f) =>
              captured.elimStep(e.resultVar) match {
                case NotFound() => Closure(captured, e, snd(f))
                case other => UnhandledCase.raise(s"$other")
              }
            case HalfUsed(f, u) =>
              captured.elimStep(u) match {
                case NotFound()               => HalfUsed(f.withCaptured(captured).map(assocRL), u)
                case Exact(_, h)              => f.map(snd(h) > swap)
                case Closure(captured1, _, h) => f.withCaptured(captured1).map(snd(swap) > assocRL > fst(h))
                case HalfUsed(g, w)           => HalfUsed(ElimStep.thenSnd(f, g) map (assocRL > fst(swap)), w)
              }
            case other @ Closure(_, _, _) =>
              UnhandledCase.raise(s"$other")
          }
      }

      case class Exact[V, B](expr: Expr.VarDefining[V], f: V ≈⚬ B) extends Found[V, B]
      case class Closure[X, V, B](captured: Expr[X], expr: Expr[V], f: (X |*| V) ≈⚬ B) extends Found[V, B]
      case class HalfUsed[V, B, U](f: Found[V, B |*| U], unused: Var[U]) extends Found[V, B]

      def halfUsed1[V, B, U](step: ElimStep[V, B |*| U], u: Var[U]): ElimStep[V, B] =
        step match {
          case NotFound()               => NotFound()
          case found: Found[V, B |*| U] => HalfUsed(found, u)
        }

      def halfUsed2[V, U, B](step: ElimStep[V, U |*| B], u: Var[U]): ElimStep[V, B] =
        halfUsed1(step.map(swap[U, B]), u)

      def closure[X, V, W, B](captured: Expr[X], f: Found[V, W], g: (X |*| W) ≈⚬ B): ElimStep[V, B] =
        f.withCaptured(captured).map(g)

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
                ElimStep.Closure(f1 zip x, e2, assocLR > snd(g2))
              case other @ ElimStep.HalfUsed(_, _) =>
                UnhandledCase.raise(s"$other")
            }
          case ElimStep.Exact(e1, g1) =>
            f2.elimStep(v) match {
              case ElimStep.NotFound() =>
                ElimStep.Closure(f2, e1, snd(g1) > swap)
              case other =>
                UnhandledCase.raise(s"$other")
            }
          case other @ ElimStep.Closure(_, _, _) =>
            UnhandledCase.raise(s"$other")
          case ElimStep.HalfUsed(h1, u) =>
            f2.elimStep(u) match {
              case ElimStep.NotFound() =>
                halfUsed1(h1.withCaptured(f2).map(assocRL > fst(swap)), u)
              case ElimStep.Exact(g2, h2) =>
                h1 map snd(h2)
              case ElimStep.Closure(captured, g2, h2) =>
                h1.withCaptured(captured).map(xi > snd(h2))
              case ElimStep.HalfUsed(g2, w) =>
                ElimStep.halfUsed1(ElimStep.thenSnd(h1, g2).map(assocRL), w)
            }
        }

      def thenSnd[V, B1, X, B2](f: Found[V, B1 |*| X], g: Found[X, B2]): Found[V, B1 |*| B2] =
        g match {
          case Exact(g0, g1)   => f.map(snd(g1))
          case HalfUsed(g0, u) => HalfUsed(thenSnd(f, g0).map(assocRL), u)
          case other @ Closure(_, _, _) => UnhandledCase.raise(s"$other")
        }
    }

    sealed trait ElimRes[V, B]
    object ElimRes {
      case class Exact[V, B](expr: Expr[V], f: V ≈⚬ B) extends ElimRes[V, B]
      case class Closure[X, V, B](captured: Expr[X], expr: Expr[V], f: (X |*| V) ≈⚬ B) extends ElimRes[V, B]
      case class Unused[V, B](vars: VarSet) extends ElimRes[V, B]
    }

    def unzip[A, B1, B2](f: VArr[A, B1 |*| B2]): (VArr[A, B1], VArr[A, B2]) = {
      val b1 = newVar[B1]()
      val b2 = newVar[B2]()
      (Prj1(f, b1, b2), Prj2(f, b1, b2))
    }
  }

  type Expr[A] = VArr[?, A]

  object Expr {
    type VarDefining[A] = VArr.VarDefining[?, A]

    def variable[A](a: Var[A]): Expr[A] =
      VArr.Id(a)

    def zip[A, B](a: Expr[A], b: Expr[B]): Expr[A |*| B] =
      a zip b

    def unzip[A, B](p: Expr[A |*| B]): (Expr[A], Expr[B]) =
      VArr.unzip(p)
  }

  type Tupled[F[_], A] = libretto.impl.Tupled[|*|, F, A]

  type Vars[A] = Tupled[Var, A]
  object Vars {
    def single[A](a: Var[A]): Vars[A] =
      Tupled.Single(a)

    def bi[A, B](a: Var[A], b: Var[B]): Vars[A |*| B] =
      zip(single(a), single(b))

    def zip[A, B](a: Vars[A], b: Vars[B]): Vars[A |*| B] =
      Tupled.Zip(a, b)

    def unzip[A, B](ab: Vars[A |*| B]): Option[(Vars[A], Vars[B])] =
      Tupled.unzip(ab)

    def sameVars[A](a: Vars[A], b: Vars[A]): Boolean =
      a == b

    def toSet[A](vars: Vars[A]): VarSet =
      vars.mapReduce0(
        map    = [x] => (v: Var[x]) => variables.singleton(v),
        reduce = variables.union(_, _),
      )
  }

  extension [A](vars: Vars[A]) {
    def toSet: VarSet =
      Vars.toSet(vars)
  }

  def abs[A, B](
    f: Expr[A] => Expr[B],
  )(using
    ev: SymmetricSemigroupalCategory[-⚬, |*|],
  ): Abstracted[A, B] = {
    import VArr.ElimRes

    val v = newVar[A]()
    val b = f(Expr.variable(v))

    b.elim(v) match {
      case ElimRes.Exact(e, f) =>
        e match {
          case VArr.Id(`v`) => Abstracted.Exact(f)
          case other        => bug(s"Expected ${Expr.variable(v)}, got $other")
        }
      case ElimRes.Closure(captured, e, f) =>
        e match {
          case VArr.Id(`v`) => Abstracted.Closure(captured, f)
          case other        => bug(s"Expected ${Expr.variable(v)}, got $other")
        }
      case ElimRes.Unused(vars) =>
        Abstracted.Failure.underused(vars)
    }
  }

  def compile[A, B](
    f: Expr[A] => Expr[B],
  )(using
    ev: SymmetricSemigroupalCategory[-⚬, |*|],
  ): Either[Error, A -⚬ B] = {
    import Abstracted._

    abs(f) match {
      case Exact(f)             => Right(f.fold)
      case Closure(captured, _) => Left(Error.Undefined(captured.initialVars.toSet))
      case Failure(e)           => Left(e)
    }
  }

  sealed trait Abstracted[A, B]
  object Abstracted {
    case class Exact[A, B](
      f: A ≈⚬ B,
    ) extends Abstracted[A, B]

    case class Closure[X, A, B](
      captured: Expr[X],
      f: (X |*| A) ≈⚬ B,
    ) extends Abstracted[A, B]

    case class Failure[A, B](e: LinearityViolation) extends Abstracted[A, B]
    object Failure {
      def overused[A, B](vars: VarSet): Failure[A, B] =
        Failure(LinearityViolation.Overused(vars))

      def underused[A, B](vars: VarSet): Failure[A, B] =
        Failure(LinearityViolation.Underused(vars))
    }
  }

  sealed trait Error
  object Error {
    case class Undefined(vars: VarSet) extends Error
  }

  sealed trait LinearityViolation extends Error

  object LinearityViolation {
    case class Overused(vars: VarSet) extends LinearityViolation

    case class Underused(vars: VarSet) extends LinearityViolation

    def overused[A](v: Var[A]): LinearityViolation.Overused =
      LinearityViolation.Overused(variables.singleton(v))

    def underused[A](v: Var[A]): LinearityViolation.Underused =
      LinearityViolation.Underused(variables.singleton(v))
  }

  private def bug(msg: String): Nothing =
    throw new AssertionError(msg)
}
