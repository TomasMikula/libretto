package libretto.impl

import libretto.BiInjective

class Lambda[-⚬[_, _], |*|[_, _]](using
  inj: BiInjective[|*|],
) {

  val shuffled = new Shuffled[-⚬, |*|]
  import shuffled.shuffle.{~⚬, Transfer, TransferOpt}
  import shuffled.{Shuffled => ≈⚬, assocLR, assocRL, fst, id, ix, ixi, lift, par, pure, snd, swap, xi}

  class Var[A]() {
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

  /**
   * Arrow interspersed with intermediate [[Var]]s.
   * Non-linear: includes projections and multiple occurrences of the same variable.
   */
  sealed trait VArr[A, B] {
    import VArr._

    def resultVar: Var[B]

    def initialVars: Vars[A] =
      this match {
        case Id(a) => Vars.single(a)
        // TODO
      }

    def map[C](f: B -⚬ C): VArr[A, C] =
      Map(this, f, new Var[C])

    def zip[C, D](that: VArr[C, D]): VArr[A |*| C, B |*| D] =
      Zip(this, that, new Var[B |*| D])

    def elimStep[V](v: Var[V]): ElimStep[V, B] =
      (v testEqual resultVar) match {
        case Some(ev) =>
          ElimStep.Exact(ev.substituteContra(this), id(ev))
        case None =>
          this match {
            case Id(b) =>
              ElimStep.NotFound()
            case Map(f, g, b) =>
              f.elimStep(v).map(g)
            case Prj1(f, b1, b2) =>
              ElimStep.halfUsed1(f.elimStep(v), b2)
            case Prj2(f, b1, b2) =>
              ElimStep.halfUsed2(f.elimStep(v), b1)
            case Zip(f1: Expr[b1], f2: Expr[b2], b) =>
              ElimStep.ofZip[Expr, V, b1, b2](
                v,
                f1,
                f2,
                [w, b] => (w: Var[w], b: Expr[b]) => b elimStep w,
                [b] => (b: Expr[b]) => Exprs(b),
              )
          }
      }

    def elim[V](v: Var[V]): ElimRes[V, B] =
      this.elimStep(v) match {
        case ElimStep.NotFound()       => ElimRes.unused(v)
        case ElimStep.Exact(e, f)      => ElimRes.Exact(e, f)
        case ElimStep.Closure(x, e, f) => ElimRes.Closure(x, e, f)
        case ElimStep.HalfUsed(_, u)   => ElimRes.Unused(Set(u)) // TODO: report all half-used vars
      }
  }

  object VArr {
    case class Id[A](variable: Var[A]) extends VArr[A, A] {
      override def resultVar: Var[A] =
        variable
    }

    case class Map[A, B, C](
      f: VArr[A, B],
      g: B -⚬ C,
      resultVar: Var[C],
    ) extends VArr[A, C]

    case class Zip[A1, A2, B1, B2](
      f1: VArr[A1, B1],
      f2: VArr[A2, B2],
      resultVar: Var[B1 |*| B2],
    ) extends VArr[A1 |*| A2, B1 |*| B2]

    case class Prj1[A, B1, B2](f: VArr[A, B1 |*| B2], b1: Var[B1], b2: Var[B2]) extends VArr[A, B1] {
      override def resultVar: Var[B1] =
        b1
    }

    case class Prj2[A, B1, B2](f: VArr[A, B1 |*| B2], b1: Var[B1], b2: Var[B2]) extends VArr[A, B2] {
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

        def withCaptured[X](captured: Exprs[X]): Found[V, X |*| B] = {
          import Exprs.elimStep

          this match {
            case Exact(e, f) =>
              captured.elimStep(e.resultVar) match {
                case NotFound() => Closure(captured, e, snd(f))
                // TODO
              }
            case HalfUsed(f, u) =>
              captured.elimStep(u) match {
                case NotFound()               => HalfUsed(f.withCaptured(captured).map(assocRL), u)
                case Exact(_, h)              => f.map(snd(h) > swap)
                case Closure(captured1, _, h) => f.withCaptured(captured1).map(snd(swap) > assocRL > fst(h))
                case HalfUsed(g, w)           => HalfUsed(ElimStep.thenSnd(f, g) map (assocRL > fst(swap)), w)
              }
            // TODO
          }
        }
      }

      case class Exact[V, B](expr: Expr[V], f: V ≈⚬ B) extends Found[V, B]
      case class Closure[X, V, B](captured: Exprs[X], expr: Expr[V], f: (X |*| V) ≈⚬ B) extends Found[V, B]
      case class HalfUsed[V, B, U](f: Found[V, B |*| U], unused: Var[U]) extends Found[V, B]

      def halfUsed1[V, B, U](step: ElimStep[V, B |*| U], u: Var[U]): ElimStep[V, B] =
        step match {
          case NotFound()               => NotFound()
          case found: Found[V, B |*| U] => HalfUsed(found, u)
        }

      def halfUsed2[V, U, B](step: ElimStep[V, U |*| B], u: Var[U]): ElimStep[V, B] =
        halfUsed1(step.map(swap[U, B]), u)

      def closure[X, V, W, B](captured: Exprs[X], f: Found[V, W], g: (X |*| W) ≈⚬ B): ElimStep[V, B] =
        f.withCaptured(captured).map(g)

      def ofZip[F[_], V, B1, B2](
        v: Var[V],
        f1: F[B1],
        f2: F[B2],
        elimStep: [v, b] => (Var[v], F[b]) => ElimStep[v, b],
        exprs: [b] => F[b] => Exprs[b],
      ): ElimStep[V, B1 |*| B2] =
        elimStep(v, f1) match {
          case ElimStep.NotFound() =>
            elimStep(v, f2) match {
              case ElimStep.NotFound() =>
                ElimStep.NotFound()
              case ElimStep.Exact(e2, g2) =>
                ElimStep.Closure(exprs(f1), e2, snd(g2))
              case ElimStep.Closure(x, e2, g2) =>
                ElimStep.Closure(exprs(f1) zip x, e2, assocLR > snd(g2))
              // TODO
            }
          case ElimStep.Exact(e1, g1) =>
            elimStep(v, f2) match {
              case ElimStep.NotFound() =>
                ElimStep.Closure(exprs(f2), e1, snd(g1) > swap)
              // TODO
            }
          case ElimStep.HalfUsed(h1, u) =>
            elimStep(u, f2) match {
              case ElimStep.NotFound() =>
                halfUsed1(h1.withCaptured(exprs(f2)).map(assocRL > fst(swap)), u)
              case ElimStep.Exact(g2, h2) =>
                h1 map snd(h2)
              case ElimStep.Closure(captured, g2, h2) =>
                h1.withCaptured(captured).map(xi > snd(h2))
              case ElimStep.HalfUsed(g2, w) =>
                ElimStep.halfUsed1(ElimStep.thenSnd(h1, g2).map(assocRL), w)
            }
          // TODO
        }

      def thenSnd[V, B1, X, B2](f: Found[V, B1 |*| X], g: Found[X, B2]): Found[V, B1 |*| B2] =
        g match {
          case Exact(g0, g1)   => f.map(snd(g1))
          case HalfUsed(g0, u) => HalfUsed(thenSnd(f, g0).map(assocRL), u)
          // TODO
        }
    }

    sealed trait ElimRes[V, B]
    object ElimRes {
      case class Exact[V, B](expr: Expr[V], f: V ≈⚬ B) extends ElimRes[V, B]
      case class Closure[X, V, B](captured: Exprs[X], expr: Expr[V], f: (X |*| V) ≈⚬ B) extends ElimRes[V, B]
      case class Unused[V, B](vars: Set[Var[?]]) extends ElimRes[V, B]

      def unused[V, B](unusedVar: Var[?]): ElimRes[V, B] =
        Unused(Set(unusedVar))
    }

    def unzip[A, B1, B2](f: VArr[A, B1 |*| B2]): (VArr[A, B1], VArr[A, B2]) = {
      val b1 = new Var[B1]
      val b2 = new Var[B2]
      (Prj1(f, b1, b2), Prj2(f, b1, b2))
    }
  }

  type Expr[A] = VArr[?, A]

  object Expr {
    def variable[A](a: Var[A]): Expr[A] =
      VArr.Id(a)

    def zip[A, B](a: Expr[A], b: Expr[B]): Expr[A |*| B] =
      a zip b

    def unzip[A, B](p: Expr[A |*| B]): (Expr[A], Expr[B]) =
      VArr.unzip(p)
  }

  type Exprs[A] = Tupled[Expr, A]

  object Exprs {
    def apply[A](a: Expr[A]): Exprs[A] =
      Tupled.Single(a)

    extension [A](es: Exprs[A]) {
      def initialVars: Vars[?] =
        es.mapReduce0[Vars[?]]([x] => (ex: Expr[x]) => ex.initialVars, _ zip _)

      def elimStep[V](v: Var[V]): VArr.ElimStep[V, A] =
        es match {
          case Tupled.Single(a) =>
            a.elimStep(v)
          case Tupled.Zip(a1, a2) =>
            VArr.ElimStep.ofZip(
              v,
              a1,
              a2,
              [w, b] => (w: Var[w], b: Exprs[b]) => b elimStep w,
              [b] => (b: Exprs[b]) => b,
            )
        }
    }
  }

  sealed trait Tupled[F[_], A] {
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

    def fold(zip: [x, y] => (F[x], F[y]) => F[x |*| y]): F[A] =
      mapReduce[F]([x] => (fx: F[x]) => fx, zip)

    def trans[G[_]](f: [x] => F[x] => G[x]): Tupled[G, A] =
      this match {
        case Tupled.Single(a) => Tupled.Single(f(a))
        case Tupled.Zip(x, y) => Tupled.Zip(x.trans(f), y.trans(f))
      }
  }

  object Tupled {
    case class Single[F[_], A](v: F[A]) extends Tupled[F, A]
    case class Zip[F[_], X, Y](_1: Tupled[F, X], _2: Tupled[F, Y]) extends Tupled[F, X |*| Y]

    def unzip[F[_], A, B](ab: Tupled[F, A |*| B]): Option[(Tupled[F, A], Tupled[F, B])] =
      ab match {
        case Zip(a, b) => Some((a, b))
        case Single(_) => None
      }
  }

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

  def abs[A, B](
    f: Expr[A] => Expr[B],
  )(using
    ev: SymmetricSemigroupalCategory[-⚬, |*|],
  ): Abstracted[A, B] = {
    import VArr.ElimRes

    val v = new Var[A]()
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
    import Exprs.initialVars

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
      captured: Exprs[X],
      f: (X |*| A) ≈⚬ B,
    ) extends Abstracted[A, B]

    case class Failure[A, B](e: LinearityViolation) extends Abstracted[A, B]
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

  private def bug(msg: String): Nothing =
    throw new AssertionError(msg)
}
