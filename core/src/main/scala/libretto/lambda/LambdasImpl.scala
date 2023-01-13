package libretto.lambda

import libretto.{lambda => ll}
import libretto.lambda.Lambdas.Error.LinearityViolation
import libretto.lambda.Lambdas.ErrorFactory
import libretto.util.{Applicative, BiInjective, Exists, Masked, TypeEq}
import libretto.util.TypeEq.Refl
import scala.annotation.{tailrec, targetName}

class LambdasImpl[-⚬[_, _], |*|[_, _], Var[_], VarSet, E, LE](using
  ssc: SymmetricSemigroupalCategory[-⚬, |*|],
  inj: BiInjective[|*|],
  variables: Variable[Var, VarSet],
  errors: ErrorFactory[E, LE, VarSet],
) extends Lambdas[-⚬, |*|, Var, VarSet, E, LE] {
  import variables.testEqual

  val shuffled = Shuffled[-⚬, |*|]
  import shuffled.shuffle.{~⚬, Transfer, TransferOpt}
  import shuffled.{Shuffled => ≈⚬, assocLR, assocRL, fst, id, ix, ixi, lift, par, pure, snd, swap, xi}

  override type AbstractFun[A, B] =
    A ≈⚬ B

  override object AbstractFun extends AbstractFuns {
    override def fold[A, B](f: AbstractFun[A, B]): A -⚬ B =
      f.fold
  }

  type CapturingFun[A, B] = libretto.lambda.CapturingFun[AbstractFun, |*|, Tupled[Expr, *], A, B]
  object CapturingFun {
    def noCapture[A, B](f: AbstractFun[A, B]): CapturingFun[A, B] =
      ll.CapturingFun.NoCapture(f)

    def id[A]: CapturingFun[A, A] =
      noCapture(shuffled.id)

    def lift[A, B](f: A -⚬ B): CapturingFun[A, B] =
      noCapture(shuffled.lift(f))

    def captureFst[X, A](captured: Expr[X]): CapturingFun[A, X |*| A] =
      ll.CapturingFun.Closure(ll.Tupled.Single(captured), shuffled.id)

    def captureSnd[X, A](captured: Expr[X]): CapturingFun[A, A |*| X] =
      ll.CapturingFun.Closure(ll.Tupled.Single(captured), shuffled.swap)
  }

  /**
   * Arrow interspersed with intermediate [[Var]]s.
   * Non-linear: includes projections and multiple occurrences of the same variable.
   */
  sealed trait VArr[A, B] {
    import VArr._

    def vd: VarDefining[A, B] =
      this match
        case vd: VarDefining[A, B] => vd

    def initialVars: Vars[A] =
      this match {
        case Id(a)         => Vars.single(a)
        case Map(f, _, _)  => f.initialVars
        case Zip(f, g, _)  => f.initialVars zip g.initialVars
        case Prj1(f, _, _) => f.initialVars
        case Prj2(f, _, _) => f.initialVars
      }

    def terminalVars: Vars[B] =
      this match {
        case vd: VarDefining[A, B] => Vars.single(vd.resultVar)
      }

    def map[C](f: B -⚬ C)(resultVar: Var[C]): VArr[A, C] =
      Map(this.vd, f, resultVar)

    def zip[C, D](that: VArr[C, D])(resultVar: Var[B |*| D]): VArr[A |*| C, B |*| D] =
      Zip(this, that, resultVar)
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
      f: VarDefining[A, B],
      g: B -⚬ C,
      resultVar: Var[C],
    ) extends VarDefining[A, C]

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

    def id[A](a: Var[A]): VArr[A, A] =
      VArr.Id(a)

    def map[A, B, C](f: VArr[A, B], g: B -⚬ C, resultVar: Var[C]): VArr[A, C] =
      (f map g)(resultVar)

    def zip[A1, A2, B1, B2](f1: VArr[A1, B1], f2: VArr[A2, B2], resultVar: Var[B1 |*| B2]): VArr[A1 |*| A2, B1 |*| B2] =
      (f1 zip f2)(resultVar)

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

    override def unzip[A, B](p: Expr[A |*| B])(resultVar1: Var[A], resultVar2: Var[B]): (Expr[A], Expr[B]) =
      VArr.unzip(p)(resultVar1, resultVar2)

    override def terminalVars[A](a: Expr[A]): Vars[A] =
      VArr.terminalVars(a)
  }

  override def abs[A, B](expr: Expr[B], boundVar: Var[A]): Abstracted[A, B] = {
    import HybridArrow.TailLinearRes

    eliminate(boundVar, expr.vd) match {
      case EliminateRes.Found(arr) =>
        arr.tailLinear match {
          case TailLinearRes.Exact(m, f)             => Lambdas.Abstracted.Exact(m, f)
          case TailLinearRes.Closure(captured, m, f) => Lambdas.Abstracted.Closure(captured, m, f)
          case TailLinearRes.Violation(e)            => Lambdas.Abstracted.Failure(e)
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
  private def eliminate[A, B](v: Var[A], expr: Expr.VarDefining[B]): EliminateRes[A, B] = {
    import EliminateRes.{Found, NotFound}

    expr match
      case VArr.Id(w) =>
        testEqual(v, w) match
          case None     => NotFound()
          case Some(ev) => Found(HybridArrow.id(v).to(using ev.liftCo[Var]))
      case VArr.Map(f, g, resultVar) =>
        eliminate(v, f) match
          case NotFound() => NotFound()
          case Found(arr) => Found(arr > HybridArrow.map(g, resultVar))
      case VArr.Zip(f1, f2, resultVar) =>
        (eliminate(v, f1.vd), eliminate(v, f2.vd)) match
          case (NotFound(), NotFound()) => NotFound()
          case (NotFound(), Found(arr)) => Found(arr > HybridArrow.captureFst(f1, resultVar))
          case (Found(arr), NotFound()) => Found(arr > HybridArrow.captureSnd(f2, resultVar))
          case (Found(ar1), Found(ar2)) => Found((ar1 interweave ar2) > HybridArrow.zip(resultVar))
      case VArr.Prj1(f, b1, b2) =>
        eliminate(v, f.vd) match
          case NotFound() => NotFound()
          case Found(arr) => Found(arr > HybridArrow.prj1(b1, b2))
      case VArr.Prj2(f, b1, b2) =>
        eliminate(v, f.vd) match
          case NotFound() => NotFound()
          case Found(arr) => Found(arr > HybridArrow.prj2(b1, b2))
  }

  private enum EliminateRes[A, B] {
    case Found[A, B](arr: HybridArrow[A, Var[B]]) extends EliminateRes[A, B]
    case NotFound()
  }

  private case class HybridArrow[A, B](v: Var[A], tail: HybridArrow.Tail[Var[A], B]) {
    import HybridArrow._

    def >[C](that: Tail[B, C]): HybridArrow[A, C] =
      HybridArrow(v, tail > that)

    def to[C](using ev: B =:= C): HybridArrow[A, C] =
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

    private def pullOut[F[_], X, Y](i: Focus[|*|, F], op: Op[X, Y])(using ev: B =:= F[X]): Option[HybridArrow[A, F[X |*| Y]]] = ev match { case TypeEq(Refl()) =>
      val aux = Op.InputVarFocus(op)
      type FF[T] = F[aux.F[T]]
      aux.ev match { case TypeEq(Refl()) =>
        HybridArrow.pullOut[Var[A], FF, aux.X, aux.F, Y](tail, aux.op)(i compose aux.F, aux.F)
          .map { (res0: Tail[Var[A], F[aux.F[Var[aux.X] |*| Y]]]) =>
            val   res1: Tail[Var[A], F[aux.F[Var[aux.X]] |*| Y]] = res0 > shOp.extractSnd(aux.F).at(i)
            HybridArrow(v, res1)
          }
      }
    }

    def tailLinear[B0](using ev: B =:= Var[B0]): HybridArrow.TailLinearRes[A, B0] =
      ev match { case TypeEq(Refl()) =>
        demultiply(tail) match {
          case Demultiplied.Impl(m, tail1) =>
            Unvar.SingleVar[A]().multiply(m) match {
              case Exists.Some((u, m0)) =>
                extractLinear(v.multiply(m), tail1)(u, Unvar.SingleVar[B0]())
                  .multiplied(m0)
            }
        }
      }
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
          case u: Unzip[a1, a2] =>
            val BiInjective[|*|](va1_b1, _) = summon[(Var[a1] |*| Var[a2]) =:= B] andThen ev
            shOp.lift(Prj1[a1, a2](u.resultVar1, u.resultVar2)).to[B1](using va1_b1)
          case op: DupVar[a] =>
            val BiInjective[|*|](va_b1, _) = summon[(Var[a] |*| Var[a]) =:= B] andThen ev
            shOp.id.to[B1](using va_b1)
          case other =>
            bug(s"Did not realize that $other can be projected from")
        }

      private def projectSnd[B1, B2](using ev: B =:= (B1 |*| B2)): Tail[A, B2] =
        this match {
          case u: Unzip[a1, a2] =>
            val BiInjective[|*|](_, va2_b2) = summon[(Var[a1] |*| Var[a2]) =:= B] andThen ev
            shOp.lift(Prj2[a1, a2](u.resultVar1, u.resultVar2)).to[B2](using va2_b2)
          case op: DupVar[a] =>
            val BiInjective[|*|](_, va_b2) = summon[(Var[a] |*| Var[a]) =:= B] andThen ev
            shOp.id.to[B2](using va_b2)
          case other =>
            bug(s"Did not realize that $other can be projected from")
        }

      def gcdSimple[X, C](that: Op[Var[X], C])(using A =:= Var[X]): Option[Tail[A, B |*| C]]

      def prj1_gcd_this[T1, T2](that: Prj1[T1, T2])(using ev: A =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], Var[T1] |*| B]]

      def prj2_gcd_this[T1, T2](that: Prj2[T1, T2])(using ev: A =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], Var[T2] |*| B]]

      def unzip_gcd_this[T1, T2](that: Unzip[T1, T2])(using ev: A =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], (Var[T1] |*| Var[T2]) |*| B]]

      def terminalVars(a: Varz[A]): Varz[B]

      def asZip[P1, P2](using A =:= (P1 |*| P2)): Exists[[V1] =>> Exists[[V2] =>> (Zip[V1, V2], P1 =:= Var[V1], P2 =:= Var[V2], B =:= Var[V1 |*| V2])]]

      def maskInput: Masked[Op[*, B], A] =
        Masked[Op[*, B], A](this)
    }
    object Op {
      sealed trait Linear[A, B] extends Op[A, B]

      case class Zip[A1, A2](resultVar: Var[A1 |*| A2]) extends Op.Linear[Var[A1] |*| Var[A2], Var[A1 |*| A2]] {
        override def terminalVars(a: Varz[Var[A1] |*| Var[A2]]): Varz[Var[A1 |*| A2]] =
          Varz.Atom(resultVar)

        override def gcdSimple[X, C](that: Op[Var[X], C])(using ev: (Var[A1] |*| Var[A2]) =:= Var[X]): Option[Tail[Var[A1] |*| Var[A2], Var[A1 |*| A2] |*| C]] =
          varIsNotPair(ev.flip)

        override def prj1_gcd_this[T1, T2](that: Prj1[T1, T2])(using ev: (Var[A1] |*| Var[A2]) =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], Var[T1] |*| Var[A1 |*| A2]]] =
          varIsNotPair(ev.flip)

        override def prj2_gcd_this[T1, T2](that: Prj2[T1, T2])(using ev: (Var[A1] |*| Var[A2]) =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], Var[T2] |*| Var[A1 |*| A2]]] =
          varIsNotPair(ev.flip)

        override def unzip_gcd_this[T1, T2](that: Unzip[T1, T2])(using ev: (Var[A1] |*| Var[A2]) =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], (Var[T1] |*| Var[T2]) |*| Var[A1 |*| A2]]] = ???

        override def asZip[P1, P2](using
          ev: (Var[A1] |*| Var[A2]) =:= (P1 |*| P2),
        ): Exists[[V1] =>> Exists[[V2] =>> (Zip[V1, V2], P1 =:= Var[V1], P2 =:= Var[V2], Var[A1 |*| A2] =:= Var[V1 |*| V2])]] =
          ev match
            case BiInjective[|*|](ev1 @ TypeEq(Refl()), ev2 @ TypeEq(Refl())) =>
              Exists(Exists(this, ev1, ev2, summon))
      }

      case class Map[A, B](f: A -⚬ B, resultVar: Var[B]) extends Op.Linear[Var[A], Var[B]] {
        override def terminalVars(a: Varz[Var[A]]): Varz[Var[B]] =
          Varz.Atom(resultVar)

        override def gcdSimple[X, C](that: Op[Var[X], C])(using Var[A] =:= Var[X]): Option[Tail[Var[A], Var[B] |*| C]] =
          that match
            case Map(_, v) =>
              (testEqual(v, resultVar)) match
                case Some(TypeEq(Refl())) => Some(shOp.lift(this) > shOp.lift(DupVar()))
                case None                 => None
            case _ =>
              None

        override def prj1_gcd_this[A1, A2](that: Prj1[A1, A2])(using ev: Var[A] =:= Var[A1 |*| A2]): Option[Tail[Var[A1 |*| A2], Var[A1] |*| Var[B]]] = ???

        override def prj2_gcd_this[A1, A2](that: Prj2[A1, A2])(using ev: Var[A] =:= Var[A1 |*| A2]): Option[Tail[Var[A1 |*| A2], Var[A2] |*| Var[B]]] = ???

        override def unzip_gcd_this[T1, T2](that: Unzip[T1, T2])(using ev: Var[A] =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], (Var[T1] |*| Var[T2]) |*| Var[B]]] = ???

        override def asZip[P1, P2](using ev: Var[A] =:= (P1 |*| P2)): Exists[[V1] =>> Exists[[V2] =>> (Zip[V1, V2], P1 =:= Var[V1], P2 =:= Var[V2], Var[B] =:= Var[V1 |*| V2])]] =
          varIsNotPair(ev)
      }

      case class Prj1[A1, A2](resultVar: Var[A1], unusedVar: Var[A2]) extends Op[Var[A1 |*| A2], Var[A1]] {
        override def terminalVars(a: Varz[Var[A1 |*| A2]]): Varz[Var[A1]] =
          Varz.Atom(resultVar)

        override def gcdSimple[X, C](that: Op[Var[X], C])(using ev: Var[A1 |*| A2] =:= Var[X]): Option[Tail[Var[A1 |*| A2], Var[A1] |*| C]] =
          that.prj1_gcd_this(this)(using ev.flip)

        override def prj1_gcd_this[a1, a2](that: Prj1[a1, a2])(using ev: Var[A1 |*| A2] =:= Var[a1 |*| a2]): Option[Tail[Var[a1 |*| a2], Var[a1] |*| Var[A1]]] =
          (testEqual(that.resultVar, this.resultVar), testEqual(that.unusedVar, this.unusedVar)) match
            case (Some(TypeEq(Refl())), Some(TypeEq(Refl()))) =>
              Some(shOp.lift(this) > shOp.lift(DupVar()))
            case (None, None) =>
              None
            case (Some(_), None) =>
              bug(s"Variable ${that.resultVar} appeared as a result of two different projections")
            case (None, Some(_)) =>
              bug(s"Variable ${that.unusedVar} appeared as a result of two different projections")

        override def prj2_gcd_this[a1, a2](that: Prj2[a1, a2])(using
          ev: Var[A1 |*| A2] =:= Var[a1 |*| a2],
        ): Option[Tail[Var[a1 |*| a2], Var[a2] |*| Var[A1]]] =
          (testEqual(that.unusedVar, this.resultVar), testEqual(that.resultVar, this.unusedVar)) match
            case (Some(TypeEq(Refl())), Some(TypeEq(Refl()))) =>
              Some(shOp.lift(Unzip(that.unusedVar, that.resultVar)) > shOp.swap[Var[a1], Var[a2]])
            case (None, None) =>
              None
            case (Some(_), None) =>
              bug(s"Variable ${that.unusedVar} appeared as a result of two different projections")
            case (None, Some(_)) =>
              bug(s"Variable ${that.resultVar} appeared as a result of two different projections")

        override def unzip_gcd_this[T1, T2](that: Unzip[T1, T2])(using
          ev: Var[A1 |*| A2] =:= Var[T1 |*| T2],
        ): Option[Tail[Var[T1 |*| T2], (Var[T1] |*| Var[T2]) |*| Var[A1]]] =
          ev match {
            case InjectiveVar(BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl()))) =>
              (testEqual(that.resultVar1, this.resultVar), testEqual(that.resultVar2, this.unusedVar)) match
                case (Some(TypeEq(Refl())), Some(TypeEq(Refl()))) =>
                  Some(shOp.lift(that) > shOp.lift(DupVar[A1]()).inFst[Var[A2]] > shOp.ix)
                case (None, None) =>
                  None
                case (Some(_), None) =>
                  bug(s"Variable ${that.resultVar1} appeared as a result of two different projections")
                case (None, Some(_)) =>
                  bug(s"Variable ${that.resultVar2} appeared as a result of two different projections")
          }

        override def asZip[P1, P2](using ev: Var[A1 |*| A2] =:= (P1 |*| P2)): Exists[[V1] =>> Exists[[V2] =>> (Zip[V1, V2], P1 =:= Var[V1], P2 =:= Var[V2], Var[A1] =:= Var[V1 |*| V2])]] =
          varIsNotPair(ev)
      }

      case class Prj2[A1, A2](unusedVar: Var[A1], resultVar: Var[A2]) extends Op[Var[A1 |*| A2], Var[A2]] {
        override def terminalVars(a: Varz[Var[A1 |*| A2]]): Varz[Var[A2]] =
          Varz.Atom(resultVar)

        override def gcdSimple[X, C](that: Op[Var[X], C])(using ev: Var[A1 |*| A2] =:= Var[X]): Option[Tail[Var[A1 |*| A2], Var[A2] |*| C]] =
          that.prj2_gcd_this(this)(using ev.flip)

        override def prj1_gcd_this[a1, a2](that: Prj1[a1, a2])(using ev: Var[A1 |*| A2] =:= Var[a1 |*| a2]): Option[Tail[Var[a1 |*| a2], Var[a1] |*| Var[A2]]] =
          (testEqual(that.resultVar, this.unusedVar), testEqual(that.unusedVar, this.resultVar)) match
            case (Some(TypeEq(Refl())), Some(TypeEq(Refl()))) =>
              Some(shOp.lift(Unzip(that.resultVar, this.resultVar)))
            case (None, None) =>
              None
            case (Some(_), None) =>
              bug(s"Variable ${that.resultVar} appeared as a result of two different projections")
            case (None, Some(_)) =>
              bug(s"Variable ${that.unusedVar} appeared as a result of two different projections")

        override def prj2_gcd_this[a1, a2](that: Prj2[a1, a2])(using ev: Var[A1 |*| A2] =:= Var[a1 |*| a2]): Option[Tail[Var[a1 |*| a2], Var[a2] |*| Var[A2]]] =
          (testEqual(that.unusedVar, this.unusedVar), testEqual(that.resultVar, this.resultVar)) match
            case (Some(TypeEq(Refl())), Some(TypeEq(Refl()))) =>
              Some(shOp.lift(this) > shOp.lift(DupVar()))
            case (None, None) =>
              None
            case (Some(_), None) =>
              bug(s"Variable ${that.unusedVar} appeared as a result of two different projections")
            case (None, Some(_)) =>
              bug(s"Variable ${that.resultVar} appeared as a result of two different projections")

        override def unzip_gcd_this[T1, T2](that: Unzip[T1, T2])(using ev: Var[A1 |*| A2] =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], (Var[T1] |*| Var[T2]) |*| Var[A2]]] =
          (testEqual(that.resultVar1, this.unusedVar), testEqual(that.resultVar2, this.resultVar)) match
            case (Some(TypeEq(Refl())), Some(TypeEq(Refl()))) =>
              Some(shOp.lift(that) > shOp.snd(shOp.lift(DupVar())) > shOp.assocRL)
            case (None, None) =>
              None
            case (Some(_), None) =>
              bug(s"Variable ${that.resultVar1} appeared as a result of two different projections")
            case (None, Some(_)) =>
              bug(s"Variable ${that.resultVar2} appeared as a result of two different projections")

        override def asZip[P1, P2](using ev: Var[A1 |*| A2] =:= (P1 |*| P2)): Exists[[V1] =>> Exists[[V2] =>> (Zip[V1, V2], P1 =:= Var[V1], P2 =:= Var[V2], Var[A2] =:= Var[V1 |*| V2])]] =
          varIsNotPair(ev)
      }

      case class Unzip[A1, A2](resultVar1: Var[A1], resultVar2: Var[A2]) extends Op.Linear[Var[A1 |*| A2], Var[A1] |*| Var[A2]] {
        override def terminalVars(a: Varz[Var[A1 |*| A2]]): Varz[Var[A1] |*| Var[A2]] =
          Varz.Zip(Varz.Atom(resultVar1), Varz.Atom(resultVar2))

        override def gcdSimple[X, C](that: Op[Var[X], C])(using ev: Var[A1 |*| A2] =:= Var[X]): Option[Tail[Var[A1 |*| A2], Var[A1] |*| Var[A2] |*| C]] =
          that.unzip_gcd_this(this)(using ev.flip)

        override def prj1_gcd_this[a1, a2](that: Prj1[a1, a2])(using
          ev: Var[A1 |*| A2] =:= Var[a1 |*| a2],
        ): Option[Tail[Var[a1 |*| a2], Var[a1] |*| (Var[A1] |*| Var[A2])]] =
          (testEqual(that.resultVar, this.resultVar1), testEqual(that.unusedVar, this.resultVar2)) match
            case (Some(TypeEq(Refl())), Some(TypeEq(Refl()))) =>
              Some(shOp.lift(this) > shOp.fst(shOp.lift(DupVar())) > shOp.assocLR)
            case (None, None) =>
              None
            case (Some(_), None) =>
              bug(s"Variable ${that.resultVar} appeared as a result of two different projections")
            case (None, Some(_)) =>
              bug(s"Variable ${that.unusedVar} appeared as a result of two different projections")

        override def prj2_gcd_this[a1, a2](that: Prj2[a1, a2])(using
          ev: Var[A1 |*| A2] =:= Var[a1 |*| a2],
        ): Option[Tail[Var[a1 |*| a2], Var[a2] |*| (Var[A1] |*| Var[A2])]] =
          (testEqual(that.unusedVar, this.resultVar1), testEqual(that.resultVar, this.resultVar2)) match
            case (Some(TypeEq(Refl())), Some(TypeEq(Refl()))) =>
              Some(shOp.lift(this) > shOp.snd(shOp.lift(DupVar())) > shOp.xi)
            case (None, None) =>
              None
            case (Some(_), None) =>
              bug(s"Variable ${that.unusedVar} appeared as a result of two different projections")
            case (None, Some(_)) =>
              bug(s"Variable ${that.resultVar} appeared as a result of two different projections")

        override def unzip_gcd_this[T1, T2](that: Unzip[T1, T2])(using
          ev: Var[A1 |*| A2] =:= Var[T1 |*| T2],
        ): Option[Tail[Var[T1 |*| T2], (Var[T1] |*| Var[T2]) |*| (Var[A1] |*| Var[A2])]] =
          (testEqual(that.resultVar1, this.resultVar1), testEqual(that.resultVar2, this.resultVar2)) match
            case (Some(TypeEq(Refl())), Some(TypeEq(Refl()))) =>
              Some(shOp.lift(this) > shOp.par(shOp.lift(DupVar()), shOp.lift(DupVar())) > shOp.ixi)
            case (None, None) =>
              None
            case (Some(_), None) =>
              bug(s"Variable ${that.resultVar1} appeared as a result of two different projections")
            case (None, Some(_)) =>
              bug(s"Variable ${that.resultVar2} appeared as a result of two different projections")

        override def asZip[P1, P2](using ev: Var[A1 |*| A2] =:= (P1 |*| P2)): Exists[[V1] =>> Exists[[V2] =>> (Zip[V1, V2], P1 =:= Var[V1], P2 =:= Var[V2], (Var[A1] |*| Var[A2]) =:= Var[V1 |*| V2])]] =
          varIsNotPair(ev)
      }

      case class DupVar[A]() extends Op[Var[A], Var[A] |*| Var[A]] {
        override def terminalVars(a: Varz[Var[A]]): Varz[Var[A] |*| Var[A]] =
          Varz.Zip(a, a)

        override def gcdSimple[X, C](that: Op[Var[X], C])(using Var[A] =:= Var[X]): Option[Tail[Var[A], Var[A] |*| Var[A] |*| C]] = ???

        override def prj1_gcd_this[T1, T2](that: Prj1[T1, T2])(using ev: Var[A] =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], Var[T1] |*| (Var[A] |*| Var[A])]] = ???

        override def prj2_gcd_this[T1, T2](that: Prj2[T1, T2])(using ev: Var[A] =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], Var[T2] |*| (Var[A] |*| Var[A])]] = ???

        override def unzip_gcd_this[T1, T2](that: Unzip[T1, T2])(using ev: Var[A] =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], (Var[T1] |*| Var[T2]) |*| (Var[A] |*| Var[A])]] = ???

        override def asZip[P1, P2](using ev: Var[A] =:= (P1 |*| P2)): Exists[[V1] =>> Exists[[V2] =>> (Zip[V1, V2], P1 =:= Var[V1], P2 =:= Var[V2], (Var[A] |*| Var[A]) =:= Var[V1 |*| V2])]] =
          varIsNotPair(ev)
      }

      case class CaptureFst[A, X](x: Expr[X], resultVar: Var[X |*| A]) extends Op.Linear[Var[A], Var[X |*| A]] {
        override def terminalVars(a: Varz[Var[A]]): Varz[Var[X |*| A]] =
          Varz.Atom(resultVar)

        override def gcdSimple[Q, C](that: Op[Var[Q], C])(using Var[A] =:= Var[Q]): Option[Tail[Var[A], Var[X |*| A] |*| C]] = ???

        override def prj1_gcd_this[T1, T2](that: Prj1[T1, T2])(using ev: Var[A] =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], Var[T1] |*| Var[X |*| A]]] = ???

        override def prj2_gcd_this[T1, T2](that: Prj2[T1, T2])(using ev: Var[A] =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], Var[T2] |*| Var[X |*| A]]] = ???

        override def unzip_gcd_this[T1, T2](that: Unzip[T1, T2])(using ev: Var[A] =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], (Var[T1] |*| Var[T2]) |*| Var[X |*| A]]] = ???

        override def asZip[P1, P2](using ev: Var[A] =:= (P1 |*| P2)): Exists[[V1] =>> Exists[[V2] =>> (Zip[V1, V2], P1 =:= Var[V1], P2 =:= Var[V2], Var[X |*| A] =:= Var[V1 |*| V2])]] =
          varIsNotPair(ev)
      }

      case class CaptureSnd[A, X](x: Expr[X], resultVar: Var[A |*| X]) extends Op.Linear[Var[A], Var[A |*| X]] {
        override def terminalVars(a: Varz[Var[A]]): Varz[Var[A |*| X]] =
          Varz.Atom(resultVar)

        override def gcdSimple[Q, C](that: Op[Var[Q], C])(using Var[A] =:= Var[Q]): Option[Tail[Var[A], Var[A |*| X] |*| C]] = ???

        override def prj1_gcd_this[T1, T2](that: Prj1[T1, T2])(using ev: Var[A] =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], Var[T1] |*| Var[A |*| X]]] = ???

        override def prj2_gcd_this[T1, T2](that: Prj2[T1, T2])(using ev: Var[A] =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], Var[T2] |*| Var[A |*| X]]] = ???

        override def unzip_gcd_this[T1, T2](that: Unzip[T1, T2])(using ev: Var[A] =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], (Var[T1] |*| Var[T2]) |*| Var[A |*| X]]] = ???

        override def asZip[P1, P2](using ev: Var[A] =:= (P1 |*| P2)): Exists[[V1] =>> Exists[[V2] =>> (Zip[V1, V2], P1 =:= Var[V1], P2 =:= Var[V2], Var[A |*| X] =:= Var[V1 |*| V2])]] =
          varIsNotPair(ev)
      }

      val project: [t, u, v] => (op: Op[t, u], p: Projection[|*|, u, v]) => shOp.ProjectRes[t, v] =
        [t, u, v] => (op: Op[t, u], p: Projection[|*|, u, v]) => op.project(p)

      sealed trait InputVarFocus[A, B] {
        type F[_]
        type X
        val F: Focus[|*|, F]
        val ev: A =:= F[Var[X]]
        val op: Op[F[Var[X]], B]
      }

      object InputVarFocus {
        def apply[G[_], T, B](op0: Op[G[Var[T]], B], g: Focus[|*|, G]): InputVarFocus[G[Var[T]], B] =
          new InputVarFocus[G[Var[T]], B] {
            override type F[A] = G[A]
            override type X = T
            override val F = g
            override val ev = summon
            override val op = op0
          }

        def apply[A, B](op: Op[A, B]): InputVarFocus[A, B] =
          op match {
            case op: DupVar[t]   => InputVarFocus[[x] =>> x, t, Var[t] |*| Var[t]](op, Focus.id)
            case op: Zip[t, u]   => InputVarFocus[[x] =>> x |*| Var[u], t, Var[t |*| u]](op, Focus.fst) // arbitrarily picking the first input
            case op: Unzip[t, u] => InputVarFocus[[x] =>> x, t |*| u, Var[t] |*| Var[u]](op, Focus.id)
            case op: Prj1[t, u]  => InputVarFocus[[x] =>> x, t |*| u, Var[t]](op, Focus.id)
            case op: Prj2[t, u]  => InputVarFocus[[x] =>> x, t |*| u, Var[u]](op, Focus.id)
            case op: Map[t, u]   => InputVarFocus[[x] =>> x, t, Var[u]](op, Focus.id)
            case CaptureFst(x, resultVar) => ???
            case CaptureSnd(x, resultVar) => ???
          }
      }

      def gcd[C[_], D[_], X, Y, Z](
        f: Op[C[Var[X]], Y],
        g: Op[D[Var[X]], Z],
      )(
        C: Focus[|*|, C],
        D: Focus[|*|, D],
      ): Option[Tail[C[Var[X]], Y |*| Z]] = {
        import shOp.shuffle.{zip => zipEq}

        (C, D) match {
          case (Focus.Id(), Focus.Id()) =>
            f gcdSimple g
          case (c: Focus.Fst[p, c1, y], d: Focus.Fst[q, d1, z]) =>
            f.asZip[c1[Var[X]], y] match
              case e1 @ Exists.Some(e2 @ Exists.Some((z1, ev1 @ TypeEq(Refl()), TypeEq(Refl()), TypeEq(Refl())))) =>
                g.asZip[d1[Var[X]], z] match
                  case e3 @ Exists.Some(e4 @ Exists.Some(z2, ev2, TypeEq(Refl()), TypeEq(Refl()))) =>
                    gcdZips(z1, z2).map(_.from(using ev1 zipEq summon[y =:= Var[e2.T]]))
          case (c: Focus.Snd[p, c2, y], d: Focus.Snd[q, d2, z]) =>
            f.asZip[y, c2[Var[X]]] match
              case e1 @ Exists.Some(e2 @ Exists.Some((z1, ev1 @ TypeEq(Refl()), ev2 @ TypeEq(Refl()), TypeEq(Refl())))) =>
                g.asZip[z, d2[Var[X]]] match
                  case e3 @ Exists.Some(e4 @ Exists.Some(z2, TypeEq(Refl()), TypeEq(Refl()), TypeEq(Refl()))) =>
                    gcdZips(z1, z2).map(_.from[y |*| c2[Var[X]]](using ev1 zipEq ev2))
          case _ =>
            // TODO: derive contradiction
            UnhandledCase.raise(s"($f at $C) gcd ($g at $D)")
        }
      }

      private def gcdZips[A1, A2, B1, B2](
        z1: Zip[A1, A2],
        z2: Zip[B1, B2],
      ): Option[Tail[Var[A1] |*| Var[A2], Var[A1 |*| A2] |*| Var[B1 |*| B2]]] =
        testEqual(z1.resultVar, z2.resultVar) map {
          case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
            shOp.lift(z1) > shOp.lift(DupVar())
        }
    }

    enum Varz[A] {
      case Atom[V](v: Var[V]) extends Varz[Var[V]]
      case Zip[A, B](a: Varz[A], b: Varz[B]) extends Varz[A |*| B]

      def get[V](using ev: A =:= Var[V]): Var[V] =
        this match {
          case Atom(v) => v
          case _: Zip[a, b] => varIsNotPair[V, a, b](ev.flip)
        }

      def unzip[X, Y](using ev: A =:= (X |*| Y)): (Varz[X], Varz[Y]) =
        this match {
          case z: Zip[a, b] =>
            (summon[(a |*| b) =:= A] andThen ev) match { case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
              (z.a, z.b)
            }
          case _: Atom[v] =>
            varIsNotPair(summon[Var[v] =:= A] andThen ev)
        }
    }

    object Varz {
      given Cartesian[|*|, Varz] with {
        override def zip[A, B](a: Varz[A], b: Varz[B]): Varz[A |*| B] =
          Zip(a, b)

        override def unzip[A, B](ab: Varz[A |*| B]): (Varz[A], Varz[B]) =
          ab.unzip
      }
    }

    val shOp = Shuffled[Op, |*|](shuffled.shuffle)
    import shOp.shuffle.{zip => zipEq}

    type VarOp[A, B] = (Varz[A], Op[A, B])
    given shVOp: Shuffled.With[VarOp, |*|, shuffled.shuffle.type] =
      Shuffled[VarOp, |*|](shuffled.shuffle)

    given shLOp: Shuffled.With[Op.Linear, |*|, shuffled.shuffle.type] =
      Shuffled[Op.Linear, |*|](shuffled.shuffle)

    enum CaptureOp[A, B] {
      case Id[A]() extends CaptureOp[A, A]
      case CaptureFst[X, A](captured: Expr[X]) extends CaptureOp[A, X |*| A]
      case CaptureSnd[A, X](captured: Expr[X]) extends CaptureOp[A, A |*| X]
    }
    type CapFun[A, B] = Either[CaptureOp[A, B], A -⚬ B]
    object CapFun {
      def id[A]: CapFun[A, A] =
        Left(CaptureOp.Id())

      def captureFst[X, A](captured: Expr[X]): CapFun[A, X |*| A] =
        Left(CaptureOp.CaptureFst(captured))

      def captureSnd[A, X](captured: Expr[X]): CapFun[A, A |*| X] =
        Left(CaptureOp.CaptureSnd(captured))

      def lift[A, B](f: A -⚬ B): CapFun[A, B] =
        Right(f)
    }
    given shCap: Shuffled.With[CapFun, |*|, shuffled.shuffle.type] =
      Shuffled[CapFun, |*|](shuffled.shuffle)

    type Tail[A, B] =
      shOp.Shuffled[A, B]

    type VTail[A, B] =
      shVOp.Shuffled[A, B]

    type LTail[A, B] =
      shLOp.Shuffled[A, B]

    type CTail[A, B] =
      shCap.Shuffled[A, B]

    def id[A](v: Var[A]): HybridArrow[A, Var[A]] =
      HybridArrow(v, shOp.id)

    def dupVar[A]: Tail[Var[A], Var[A] |*| Var[A]] =
      shOp.lift(Op.DupVar())

    def map[A, B](f: A -⚬ B, resultVar: Var[B]): Tail[Var[A], Var[B]] =
      shOp.lift(Op.Map(f, resultVar))

    def captureFst[A, X](x: Expr[X], resultVar: Var[X |*| A]): Tail[Var[A], Var[X |*| A]] =
      shOp.lift(Op.CaptureFst(x, resultVar))

    def captureSnd[A, X](x: Expr[X], resultVar: Var[A |*| X]): Tail[Var[A], Var[A |*| X]] =
      shOp.lift(Op.CaptureSnd(x, resultVar))

    def zip[A1, A2](resultVar: Var[A1 |*| A2]): Tail[Var[A1] |*| Var[A2], Var[A1 |*| A2]] =
      shOp.lift(Op.Zip(resultVar))

    // def unzip[A, A1, A2](u: Untag[A, A1 |*| A2], resultVar1: Var[A1], resultVar2: Var[A2]): Tail[A, Var[A1] |*| Var[A2]] =
    //   shOp.lift(Op.Unzip(u, resultVar1, resultVar2))

    def prj1[A1, A2](resultVar: Var[A1], unusedVar: Var[A2]): Tail[Var[A1 |*| A2], Var[A1]] =
      shOp.lift(Op.Prj1(resultVar, unusedVar))

    def prj2[A1, A2](unusedVar: Var[A1], resultVar: Var[A2]): Tail[Var[A1 |*| A2], Var[A2]] =
      shOp.lift(Op.Prj2(unusedVar, resultVar))

    /** If `op` introduces a new variable(s), searches through `t` for an existing occurrence of `op`
     *  and channels it to the output.
     *  If `op` does not introduce new variables, or if `op` is not found in `t`, returns `None`.
     */
    def pullOut[A, G[_], X, D[_], Y](t: Tail[A, G[Var[X]]], op: Op[D[Var[X]], Y])(
      G: Focus[|*|, G],
      D: Focus[|*|, D],
    ): Option[Tail[A, G[Var[X] |*| Y]]] = {
      import shOp.ChaseBwRes

      t.chaseBw(G) match {
        case ChaseBwRes.Transported(_, _, _) =>
          None
        case r: ChaseBwRes.OriginatesFrom[a, f, v, w, x, g] =>
          pullBump(r.pre, r.f, r.post, op)(r.i, r.w, D)
            .map(_ > shOp.absorbSnd(G))
        case ChaseBwRes.Split(ev) =>
          varIsNotPair(ev)
      }
    }

    def pullBump[A, F[_], V, CX, C[_], X, D[_], G[_], Y](
      pre: Tail[A, F[V]],
      obstacle: Op[V, CX],
      post: Tail[F[C[Var[X]]], G[Var[X]]],
      op: Op[D[Var[X]], Y],
    )(
      F: Focus[|*|, F],
      C: Focus[|*|, C],
      D: Focus[|*|, D],
    )(using
      ev: CX =:= C[Var[X]],
    ): Option[Tail[A, G[Var[X]] |*| Y]] = {
      obstacle match
        case o: Op.DupVar[v0] =>
          val ev1 = ev.flip andThen summon[CX =:= (Var[v0] |*| Var[v0])]
          (ev1.deriveEquality(C): X =:= v0) match { case TypeEq(Refl()) =>
            pullBumpDupVar[A, F, v0, C, D, G, Y](pre, post, op)(F, C, D)(using
              ev1,
            )
          }
        case Op.Zip(resultVar) =>
          None
        case Op.CaptureFst(x, resultVar) =>
          UnhandledCase.raise(s"$obstacle at $C followed by $op at $D")
        case Op.CaptureSnd(x, resultVar) =>
          UnhandledCase.raise(s"$obstacle at $C followed by $op at $D")
        case Op.Unzip(resultVar1, resultVar2) =>
          None
        case Op.Map(f, resultVar) =>
          None
        case Op.Prj1(resultVar, unusedVar) =>
          None
        case Op.Prj2(unusedVar, resultVar) =>
          None
    }

    def pullBumpDupVar[A, F[_], V, C[_], D[_], G[_], Y](
      pre: Tail[A, F[Var[V]]],
      post: Tail[F[C[Var[V]]], G[Var[V]]],
      op: Op[D[Var[V]], Y],
    )(
      F: Focus[|*|, F],
      C: Focus[|*|, C],
      D: Focus[|*|, D],
    )(using
      ev: C[Var[V]] =:= (Var[V] |*| Var[V]),
    ): Option[Tail[A, G[Var[V]] |*| Y]] = ev match { case TypeEq(Refl()) =>
      C match
        case c: Focus.Fst[pair, c1, q] =>
          (summon[(c1[Var[V]] |*| q) =:= C[Var[V]]] andThen ev) match { case BiInjective[|*|](c1vv_vv @ TypeEq(Refl()), q_vv @ TypeEq(Refl())) =>
            c.i match
              case Focus.Id() =>
                (summon[Var[V] =:= c1[Var[V]]] andThen c1vv_vv) match { case TypeEq(Refl()) =>
                  pushOut[[x] =>> F[Var[V] |*| x], V, D, Y, G[Var[V]]](post, op)(F compose Focus.snd[|*|, Var[V]], D) match
                    case Some(post1) =>
                      ???
                    case None =>
                      pullOut[A, F, V, D, Y](pre.to[F[Var[V]]], op)(F, D) match
                        case Some(pre1) =>
                          val post1: Tail[F[Var[V]], G[Var[V]]] = shOp.lift(Op.DupVar[V]()).to[C[Var[V]]].at(F) > post
                          Some(pre1 > shOp.extractSnd[F, Var[V], Y](F) > post1.inFst)
                        case None =>
                          ???
                }
              case Focus.Fst(_) =>
                throw new AssertionError() // TODO: derive contradiction
              case Focus.Snd(_) =>
                throw new AssertionError() // TODO: derive contradiction
          }
        case c: Focus.Snd[pair, c2, p] =>
          (summon[(p |*| c2[Var[V]]) =:= C[Var[V]]] andThen ev) match { case BiInjective[|*|](TypeEq(Refl()), c2vv_vv @ TypeEq(Refl())) =>
            c.i match
              case Focus.Id() =>
                (summon[Var[V] =:= c2[Var[V]]] andThen c2vv_vv) match { case TypeEq(Refl()) =>
                  pushOut[[x] =>> F[x |*| Var[V]], V, D, Y, G[Var[V]]](post, op)(F compose Focus.fst[|*|, Var[V]], D) match
                    case Some(post1) =>
                      Some(pre > shOp.lift(Op.DupVar[V]()).to[Var[V] |*| Var[V]].at(F) > post1)
                    case None =>
                      ???
                }
              case Focus.Fst(_) =>
                throw new AssertionError() // TODO: derive contradiction
              case Focus.Snd(_) =>
                throw new AssertionError() // TODO: derive contradiction
          }
        case Focus.Id() =>
          varIsNotPair(summon[Var[V] =:= (Var[V] |*| Var[V])])
    }

    def pushOut[F[_], X, D[_], Y, B](t: Tail[F[Var[X]], B], op: Op[D[Var[X]], Y])(
      F: Focus[|*|, F],
      D: Focus[|*|, D],
    ): Option[Tail[F[Var[X]], B |*| Y]] =
      t.chaseFw(F) match {
        case r: shOp.ChaseFwRes.FedTo[f, x, v, w, g, b] =>
          pushBump(r.pre(()), r.f, r.post, op)(r.v, r.g, D)
        case shOp.ChaseFwRes.Transported(_, _, _) =>
          None
        case shOp.ChaseFwRes.Split(_) =>
          bug(s"Unexpected pair of expressions fed to $op")
      }

    def pushBump[A, X, C[_], W, G[_], B, D[_], Y](
      pre: Tail[A, G[C[Var[X]]]],
      obstacle: Op[C[Var[X]], W],
      post: Tail[G[W], B],
      op: Op[D[Var[X]], Y],
    )(
      C: Focus[|*|, C],
      G: Focus[|*|, G],
      D: Focus[|*|, D],
    ): Option[Tail[A, B |*| Y]] =
      Op.gcd(obstacle, op)(C, D)
        .map { (res0: Tail[C[Var[X]], W |*| Y]) =>
          pre > res0.at(G) > shOp.extractSnd[G, W, Y](G) > post.inFst[Y]
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

    def demultiply[V, B](t: Tail[Var[V], B]): Demultiplied[V, B] =
      demultiplyAt[[x] =>> x, V, B](t)(Focus.id[|*|]) match {
        case DemultipliedAt.Impl(m, t) => Demultiplied.Impl(m, t)
      }

    def demultiplyAt[F[_], X, B](t: Tail[F[Var[X]], B])(F: Focus[|*|, F]): DemultipliedAt[F, X, B] =
      t.chaseFw(F) match {
        case bumped: shOp.ChaseFwRes.FedTo[f, vx, v, w, g, b] =>
          def go[V[_], W, G[_]](bumped: shOp.ChaseFwRes.FedTo[F, Var[X], V, W, G, B]): DemultipliedAt[F, X, B] = {
            bumped.f.maskInput.visit[DemultipliedAt[F, X, B]]([VVX] => (op: Op[VVX, W], ev: VVX =:= V[Var[X]]) => {
              op match {
                case op: Op.DupVar[y] =>
                  bumped.v match {
                    case Focus.Id() =>
                      summon[V[Var[X]] =:= Var[X]]
                      summon[Var[y] =:= VVX]
                      type G1[T] = G[T |*| Var[y]]
                      demultiplyAt[G1, y, B](bumped.post)(bumped.g compose Focus.fst) match {
                        case d: DemultipliedAt.Impl[g1, y, a, b] =>
                          type G2[T] = G[a |*| T]
                          demultiplyAt[G2, y, B](d.t)(bumped.g compose Focus.snd) match {
                            case DemultipliedAt.Impl(m2, t) =>
                              DemultipliedAt.Impl(Multiplier.dup(d.m, m2).from(using ev.flip), bumped.pre(()) > t)
                          }
                      }
                    case _: Focus.Fst[pair, v1, z] =>
                      varIsNotPair(summon[Var[y] =:= VVX] andThen ev andThen summon[V[Var[X]] =:= (v1[Var[X]] |*| z)])
                    case _: Focus.Snd[pair, v2, z] =>
                      varIsNotPair(summon[Var[y] =:= VVX] andThen ev andThen summon[V[Var[X]] =:= (z |*| v2[Var[X]])])
                  }
                case other =>
                  DemultipliedAt.Impl(Multiplier.id[|*|, Var[X]], t)
              }
            })
          }
          go(bumped)
        case shOp.ChaseFwRes.Transported(_, _, _) =>
          DemultipliedAt.Impl(Multiplier.id[|*|, Var[X]], t)
        case shOp.ChaseFwRes.Split(ev) =>
          varIsNotPair(ev)
      }

    enum Demultiplied[V, B] {
      case Impl[V, A, B](
        m: Multiplier[|*|, Var[V], A],
        t: Tail[A, B],
      ) extends Demultiplied[V, B]
    }

    enum DemultipliedAt[F[_], V, B] {
      case Impl[F[_], V, A, B](
        m: Multiplier[|*|, Var[V], A],
        t: Tail[F[A], B],
      ) extends DemultipliedAt[F, V, B]
    }

    def extractLinear[A, B, X, Y](a: Varz[A], t: Tail[A, B])(u: Unvar[A, X], v: Unvar[B, Y]): LinearRes[X, Y] = {
      val vt: VTail[A, B] =
        t.sweepL[Varz, VarOp](
          a,
          [p, q] => (p: Varz[p], op: Op[p, q]) => {
            val q = op.terminalVars(p)
            ((p, op), q)
          }
        )._1

      vt.traverse[LinCheck, Op.Linear](
        [p, q] => (op: VarOp[p, q]) => linearOp(op._1, op._2),
      ) match {
        case LinCheck.Success(tl) =>
          val t1: CapturingFun[X, Y] = unvar(tl)(u, v)
          t1 match {
            case ll.CapturingFun.NoCapture(f)  => LinearRes.Exact(f)
            case ll.CapturingFun.Closure(x, f) => LinearRes.Closure(x, f)
          }
        case LinCheck.Failure(e) =>
          LinearRes.Violation(e)
      }
    }

    def linearOp[A, B](vs: Varz[A], op: Op[A, B]): LinCheck[Op.Linear[A, B]] =
      op match {
        case op: Op.DupVar[a] =>
          val v = vs.get[a]
          LinCheck.Failure(errors.overusedVars(variables.singleton(v)))
        case op: Op.Linear[a, b] =>
          LinCheck.Success(op)
        case other =>
          UnhandledCase.raise(s"$other")
      }

    def unvar[A, B, X, Y](t: LTail[A, B])(u: Unvar[A, X], v: Unvar[B, Y]): CapturingFun[X, Y] =
      given shCFun: Shuffled[CapturingFun, |*|] =
        Shuffled[CapturingFun, |*|](shuffled.shuffle)
      t.translate[CapturingFun, |*|, Unvar, X](u, Unvar.objectMap, Unvar.arrowMap) match {
        case Exists.Some((t1, v1)) =>
          (v uniqueOutType v1) match {
            case TypeEq(Refl()) =>
              t1.fold
          }
      }

    enum LinearRes[A, B] {
      case Exact(f: AbstractFun[A, B])
      case Closure[X, A, B](captured: Tupled[Expr, X], f: AbstractFun[X |*| A, B]) extends LinearRes[A, B]
      case Violation(e: LE)

      def multiplied[A0](m: Multiplier[|*|, A0, A]): TailLinearRes[A0, B] =
        this match
          case Exact(f)             => TailLinearRes.Exact(m, f)
          case Closure(captured, f) => TailLinearRes.Closure(captured, m, f)
          case Violation(e)         => TailLinearRes.Violation(e)

    }

    enum TailLinearRes[A, B] {
      case Exact[A, A1, B](m: Multiplier[|*|, A, A1], f: AbstractFun[A1, B]) extends TailLinearRes[A, B]
      case Closure[X, A, A1, B](captured: Tupled[Expr, X], m: Multiplier[|*|, A, A1], f: AbstractFun[X |*| A1, B]) extends TailLinearRes[A, B]
      case Violation(e: LE)
    }

    sealed trait Unvar[A, B] {
      def uniqueOutType[C](that: Unvar[A, C]): B =:= C

      def multiply[AA](m: Multiplier[|*|, A, AA]): Exists[[BB] =>> (Unvar[AA, BB], Multiplier[|*|, B, BB])] =
        m match {
          case Multiplier.Id() =>
            Exists((this, Multiplier.id[|*|, B]))
          case Multiplier.Dup(m1, m2) =>
            (this.multiply(m1), this.multiply(m2)) match {
              case (Exists.Some((u1, n1)), Exists.Some((u2, n2))) =>
                Exists(Unvar.Par(u1, u2), Multiplier.dup(n1, n2))
            }
        }

      def maskInput: Masked[Unvar[*, B], A] =
        Masked(this)
    }
    object Unvar {
      case class SingleVar[V]() extends Unvar[Var[V], V] {
        override def uniqueOutType[C](that: Unvar[Var[V], C]): V =:= C =
          that.maskInput.visit([VV] => (that: Unvar[VV, C], ev: VV =:= Var[V]) => {
            that match {
              case _: SingleVar[v] =>
                (summon[Var[v] =:= VV] andThen ev) match { case InjectiveVar(TypeEq(Refl())) =>
                  summon[V =:= C]
                }
              case p: Par[a1, a2, x1, x2] =>
                varIsNotPair[V, a1, a2](ev.flip andThen summon[VV =:= (a1 |*| a2)])
            }
          })
      }

      case class Par[A1, A2, X1, X2](u1: Unvar[A1, X1], u2: Unvar[A2, X2]) extends Unvar[A1 |*| A2, X1 |*| X2] {
        override def uniqueOutType[C](that: Unvar[A1 |*| A2, C]): (X1 |*| X2) =:= C =
          that.maskInput.visit([A] => (that: Unvar[A, C], ev: A =:= (A1 |*| A2)) => {
            that match {
              case p: Par[a1, a2, c1, c2] =>
                (summon[(a1 |*| a2) =:= A] andThen ev)                match { case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                  ((u1 uniqueOutType p.u1), (u2 uniqueOutType p.u2))  match { case (TypeEq(Refl()), TypeEq(Refl())) =>
                    summon[(X1 |*| X2) =:= C]
                  }
                }
              case _: SingleVar[v] =>
                varIsNotPair[v, A1, A2](summon[Var[v] =:= A] andThen ev)
            }
          })
      }

      val objectMap: ObjectMap[|*|, |*|, Unvar] =
        new ObjectMap[|*|, |*|, Unvar] {
          override def uniqueOutputType[A, X, Y](f1: Unvar[A, X], f2: Unvar[A, Y]): X =:= Y =
            f1 uniqueOutType f2

          override def pair[A1, A2, X1, X2](f1: Unvar[A1, X1], f2: Unvar[A2, X2]): Unvar[A1 |*| A2, X1 |*| X2] =
            Unvar.Par(f1, f2)

          override def unpair[A1, A2, X](f: Unvar[A1 |*| A2, X]): Unpaired[A1, A2, X] =
            f.maskInput.visit[Unpaired[A1, A2, X]]([A] => (u: Unvar[A, X], ev: A =:= (A1 |*| A2)) => {
              u match {
                case p: Par[a1, a2, x1, x2] =>
                  (summon[(a1 |*| a2) =:= A] andThen ev) match { case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                    Unpaired.Impl(p.u1, p.u2)
                  }
                case _: SingleVar[v] =>
                  varIsNotPair[v, A1, A2](summon[Var[v] =:= A] andThen ev)
              }
            })
        }

      val arrowMap: ArrowMap[Op.Linear, CapturingFun, Unvar] =
        new ArrowMap[Op.Linear, CapturingFun, Unvar] {
          override def map[A, B](op: Op.Linear[A, B]): Image[A, B] =
            op match {
              case _: Op.Zip[a1, a2] =>
                Image(Par(SingleVar[a1](), SingleVar[a2]()), CapturingFun.id, SingleVar[a1 |*| a2]())
              case op: Op.Map[a, b] =>
                Image(SingleVar[a](), CapturingFun.lift(op.f), SingleVar[b]())
              case _: Op.Unzip[a1, a2] =>
                Image(SingleVar[a1 |*| a2](), CapturingFun.id, Par(SingleVar[a1](), SingleVar[a2]()))
              case op: Op.CaptureFst[a, x] =>
                Image(SingleVar[a](), CapturingFun.captureFst(op.x), SingleVar[x |*| a]())
              case op: Op.CaptureSnd[a, x] =>
                Image(SingleVar[a](), CapturingFun.captureSnd(op.x), SingleVar[a |*| x]())
            }
        }
    }

    extension [A](va: Var[A]) {
      def multiply[B](m: Multiplier[|*|, Var[A], B]): Varz[B] =
        m match {
          case Multiplier.Id() =>
            Varz.Atom(va)
          case Multiplier.Dup(m1, m2) =>
            Varz.Zip(multiply(m1), multiply(m2))
        }
    }
  }

  private def varIsNotPair[V, A, B](ev: Var[V] =:= (A |*| B)): Nothing =
    throw new AssertionError("Var[A] =:= (A |*| B)")

  extension[F[_], V, U](ev: F[Var[V]] =:= (Var[U] |*| Var[U])) {
    def deriveEquality(f: Focus[|*|, F]): V =:= U =
      f match {
        case f: Focus.Fst[pair, f1, q] =>
          (summon[(f1[Var[V]] |*| q) =:= F[Var[V]]] andThen ev) match { case BiInjective[|*|](f1v_u @ TypeEq(Refl()), TypeEq(Refl())) =>
            f.i match
              case Focus.Id() =>
                (summon[Var[V] =:= f1[Var[V]]] andThen f1v_u) match {
                  case InjectiveVar(v_u) => v_u
                }
              case _: Focus.Fst[pair, g1, t] =>
                varIsNotPair(f1v_u.flip andThen summon[f1[Var[V]] =:= (g1[Var[V]] |*| t)])
              case _: Focus.Snd[pair, g2, s] =>
                varIsNotPair(f1v_u.flip andThen summon[f1[Var[V]] =:= (s |*| g2[Var[V]])])
          }
        case f: Focus.Snd[pair, f2, p] =>
          (summon[(p|*| f2[Var[V]]) =:= F[Var[V]]] andThen ev) match { case BiInjective[|*|](TypeEq(Refl()), f2v_u @ TypeEq(Refl())) =>
            f.i match
              case Focus.Id() =>
                (summon[Var[V] =:= f2[Var[V]]] andThen f2v_u) match {
                  case InjectiveVar(v_u) => v_u
                }
              case _: Focus.Fst[pair, g1, t] =>
                varIsNotPair(f2v_u.flip andThen summon[f2[Var[V]] =:= (g1[Var[V]] |*| t)])
              case _: Focus.Snd[pair, g2, s] =>
                varIsNotPair(f2v_u.flip andThen summon[f2[Var[V]] =:= (s |*| g2[Var[V]])])
          }
        case Focus.Id() =>
          varIsNotPair(ev)
      }
  }

  // TODO: Require Injective[Var] as an argument
  private object InjectiveVar {
    def unapply[U, V](ev: Var[U] =:= Var[V]): Some[U =:= V] =
      Some(ev.asInstanceOf[U =:= V])
  }

  enum LinCheck[A] {
    case Success(value: A)
    case Failure(e: LE)
  }

  object LinCheck {
    given Applicative[LinCheck] with {
      override def pure[A](a: A): LinCheck[A] =
        Success(a)

      override def ap[A, B](ff: LinCheck[A => B])(fa: LinCheck[A]): LinCheck[B] =
        (ff, fa) match {
          case (Success(f), Success(a)) => Success(f(a))
          case (Success(_), Failure(e)) => Failure(e)
          case (Failure(e), Success(_)) => Failure(e)
          case (Failure(e), Failure(f)) => Failure(errors.combineLinear(e, f))
        }
    }
  }
}