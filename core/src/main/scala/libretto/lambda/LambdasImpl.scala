package libretto.lambda

import libretto.{lambda => ll}
import libretto.lambda.Lambdas.Error.LinearityViolation
import libretto.lambda.Lambdas.ErrorFactory
import libretto.util.{Applicative, BiInjective, Exists, Injective, Masked, TypeEq}
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
   * AST of an expression, created by user code, before translation to point-free representation,
   * containing intermediate [[Var]]s.
   * Non-linear: includes projections and multiple occurrences of the same variable.
   */
  sealed trait Expr[B] {
    import Expr._

    def resultVar: Var[B]

    def initialVars: VarSet =
      this match {
        case Id(a)         => variables.singleton(a)
        case Map(f, _, _)  => f.initialVars
        case Zip(f, g, _)  => variables.union(f.initialVars, g.initialVars)
        case Prj1(f, _, _) => f.initialVars
        case Prj2(f, _, _) => f.initialVars
      }

    def terminalVars: Vars[B] =
      Vars.single(resultVar)

    def map[C](f: B -⚬ C)(resultVar: Var[C]): Expr[C] =
      Map(this, f, resultVar)

    def zip[D](that: Expr[D])(resultVar: Var[B |*| D]): Expr[B |*| D] =
      Zip(this, that, resultVar)
  }

  object Expr extends Exprs {
    case class Id[A](variable: Var[A]) extends Expr[A] {
      override def resultVar: Var[A] =
        variable
    }

    case class Map[B, C](
      f: Expr[B],
      g: B -⚬ C,
      resultVar: Var[C],
    ) extends Expr[C]

    case class Zip[B1, B2](
      f1: Expr[B1],
      f2: Expr[B2],
      resultVar: Var[B1 |*| B2],
    ) extends Expr[B1 |*| B2]

    case class Prj1[B1, B2](f: Expr[B1 |*| B2], b1: Var[B1], b2: Var[B2]) extends Expr[B1] {
      override def resultVar: Var[B1] =
        b1
    }

    case class Prj2[B1, B2](f: Expr[B1 |*| B2], b1: Var[B1], b2: Var[B2]) extends Expr[B2] {
      override def resultVar: Var[B2] =
        b2
    }

    case class NonLinearOps[A](
      a: Expr[A],
      split: Option[A -⚬ (A |*| A)],
      discard: Option[[B] => Unit => (A |*| B) -⚬ B],
      resultVar: Var[A]
    ) extends Expr[A]

    override def variable[A](a: Var[A]): Expr[A] =
      Id(a)

    override def map[B, C](f: Expr[B], g: B -⚬ C, resultVar: Var[C]): Expr[C] =
      (f map g)(resultVar)

    override def zip[B1, B2](f1: Expr[B1], f2: Expr[B2], resultVar: Var[B1 |*| B2]): Expr[B1 |*| B2] =
      (f1 zip f2)(resultVar)

    override def unzip[B1, B2](f: Expr[B1 |*| B2])(resultVar1: Var[B1], resultVar2: Var[B2]): (Expr[B1], Expr[B2]) =
      (Prj1(f, resultVar1, resultVar2), Prj2(f, resultVar1, resultVar2))

    override def withNonLinearOps[A](a: Expr[A])(
      split: Option[A -⚬ (A |*| A)],
      discard: Option[[B] => Unit => (A |*| B) -⚬ B],
    )(
      resultVar: Var[A],
    ): Expr[A] =
      NonLinearOps(a, split, discard, resultVar)

    override def terminalVars[B](f: Expr[B]): Vars[B] =
      f.terminalVars

    def initialVars[B](f: Expr[B]): VarSet =
      f.initialVars
  }

  override def abs[A, B](boundVar: Var[A], expr: Expr[B]): Abstracted[A, B] = {
    import HybridArrow.{LinearRes, NLOpss, Op, Unvar}

    eliminate(boundVar, expr) match {
      case EliminateRes.Found(arr) =>
        HybridArrow.extract(NLOpss(Op.NLOps(None, None, arr.v)), arr.tail)(Unvar.SingleVar(), Unvar.SingleVar())  match {
          case LinearRes.Exact(f)             => Lambdas.Abstracted.Exact(f)
          case LinearRes.Closure(captured, f) => Lambdas.Abstracted.Closure(captured, f)
          case LinearRes.Violation(e)         => Lambdas.Abstracted.Failure(e)
        }
      case EliminateRes.NotFound() =>
        Lambdas.Abstracted.NotFound(expr)
    }
  }

  private def bug(msg: String): Nothing =
    throw new AssertionError(msg)

  // Note: The variable is only searched for among initial variables of the expression,
  // not in any (intermediate) results.
  private def eliminate[A, B](v: Var[A], expr: Expr[B]): EliminateRes[A, B] = {
    import EliminateRes.{Found, NotFound}

    expr match
      case Expr.Id(w) =>
        testEqual(v, w) match
          case None     => NotFound()
          case Some(ev) => Found(HybridArrow.id(v).to(using ev.liftCo[Var]))
      case Expr.Map(f, g, resultVar) =>
        eliminate(v, f) match
          case NotFound() => NotFound()
          case Found(arr) => Found(arr > HybridArrow.map(g, resultVar))
      case Expr.Zip(f1, f2, resultVar) =>
        (eliminate(v, f1), eliminate(v, f2)) match
          case (NotFound(), NotFound()) => NotFound()
          case (NotFound(), Found(arr)) => Found(arr > HybridArrow.captureFst(f1, resultVar))
          case (Found(arr), NotFound()) => Found(arr > HybridArrow.captureSnd(f2, resultVar))
          case (Found(ar1), Found(ar2)) => Found((ar1 interweave ar2) > HybridArrow.zip(resultVar))
      case Expr.Prj1(f, b1, b2) =>
        eliminate(v, f) match
          case NotFound() => NotFound()
          case Found(arr) => Found(arr > HybridArrow.prj1(b1, b2))
      case Expr.Prj2(f, b1, b2) =>
        eliminate(v, f) match
          case NotFound() => NotFound()
          case Found(arr) => Found(arr > HybridArrow.prj2(b1, b2))
      case Expr.NonLinearOps(b, split, discard, r) =>
        eliminate(v, b) match {
          case Found(arr) => Found(arr > HybridArrow.nlOps(split, discard, r))
          case NotFound() => NotFound()
        }
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

    private def weaveInOp[F[_], X, Y](i: Focus[|*|, F], op: Op[X, Y])(using ev: B =:= F[X]): HybridArrow[A, F[Y]] =
      op match {
        case _: Op.DupVar[x]=>
          HybridArrow(v, tail.to[F[X]] > shOp.lift(op).at(i))
        case op: Op.Affine[x, y] =>
          pullOut(i, op) match
            case Some(HybridArrow(v, t)) =>
              val t1 = discardFst(t, i)
              HybridArrow(v, t1)
            case None =>
              HybridArrow(v, tail.to[F[X]] > shOp.lift(op).at(i))
      }

    private def pullOut[F[_], X, Y](i: Focus[|*|, F], op: Op.Affine[X, Y])(using ev: B =:= F[X]): Option[HybridArrow[A, F[X |*| Y]]] = ev match { case TypeEq(Refl()) =>
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

      def terminalVars(a: Varz[A]): Varz[B]

      def outNLOps(a: NLOpss[A]): NLOpss[B]

      def maskInput: Masked[Op[*, B], A] =
        Masked[Op[*, B], A](this)

      def from[Z](using ev: Z =:= A): Op[Z, B] =
        ev.substituteContra[Op[*, B]](this)

      def to[C](using ev: B =:= C): Op[A, C] =
        ev.substituteCo(this)
    }
    object Op {
      sealed trait Affine[A, B] extends Op[A, B] {
        def gcdSimple[X, C](that: Op.Affine[Var[X], C])(using A =:= Var[X]): Option[Tail[A, B |*| C]]
        def prj1_gcd_this[T1, T2](that: Prj1[T1, T2])(using ev: A =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], Var[T1] |*| B]]
        def prj2_gcd_this[T1, T2](that: Prj2[T1, T2])(using ev: A =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], Var[T2] |*| B]]
        def unzip_gcd_this[T1, T2](that: Unzip[T1, T2])(using ev: A =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], (Var[T1] |*| Var[T2]) |*| B]]
        def cap1_gcd_this[T, X](that: CaptureFst[T, X])(using A =:= Var[T]): Option[Tail[Var[T], Var[X |*| T] |*| B]]
        def cap2_gcd_this[T, Y](that: CaptureSnd[T, Y])(using A =:= Var[T]): Option[Tail[Var[T], Var[T |*| Y] |*| B]]

        def asZip[P1, P2](using A =:= (P1 |*| P2)): Exists[[V1] =>> Exists[[V2] =>> (Zip[V1, V2], P1 =:= Var[V1], P2 =:= Var[V2], B =:= Var[V1 |*| V2])]]

        override def from[Z](using ev: Z =:= A): Op.Affine[Z, B] = ev.substituteContra[Op.Affine[*, B]](this)
        override def to[C](using ev: B =:= C): Op.Affine[A, C]   = ev.substituteCo(this)
      }

      sealed trait Linear[A, B] extends Affine[A, B]

      case class Zip[A1, A2](resultVar: Var[A1 |*| A2]) extends Op.Linear[Var[A1] |*| Var[A2], Var[A1 |*| A2]] {
        override def terminalVars(a: Varz[Var[A1] |*| Var[A2]]): Varz[Var[A1 |*| A2]] =
          Varz.atom(resultVar)

        override def outNLOps(a: NLOpss[Var[A1] |*| Var[A2]]): NLOpss[Var[A1 |*| A2]] =
          NLOpss(NLOps(None, None, resultVar))

        override def gcdSimple[X, C](that: Op.Affine[Var[X], C])(using ev: (Var[A1] |*| Var[A2]) =:= Var[X]): Option[Tail[Var[A1] |*| Var[A2], Var[A1 |*| A2] |*| C]] =
          varIsNotPair(ev.flip)

        override def prj1_gcd_this[T1, T2](that: Prj1[T1, T2])(using ev: (Var[A1] |*| Var[A2]) =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], Var[T1] |*| Var[A1 |*| A2]]] =
          varIsNotPair(ev.flip)

        override def prj2_gcd_this[T1, T2](that: Prj2[T1, T2])(using ev: (Var[A1] |*| Var[A2]) =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], Var[T2] |*| Var[A1 |*| A2]]] =
          varIsNotPair(ev.flip)

        override def unzip_gcd_this[T1, T2](that: Unzip[T1, T2])(using ev: (Var[A1] |*| Var[A2]) =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], (Var[T1] |*| Var[T2]) |*| Var[A1 |*| A2]]] =
          varIsNotPair(ev.flip)

        override def cap1_gcd_this[T, X](that: CaptureFst[T, X])(using ev: (Var[A1] |*| Var[A2]) =:= Var[T]): Option[Tail[Var[T], Var[X |*| T] |*| Var[A1 |*| A2]]] =
          varIsNotPair(ev.flip)

        override def cap2_gcd_this[T, Y](that: CaptureSnd[T, Y])(using ev: (Var[A1] |*| Var[A2]) =:= Var[T]): Option[Tail[Var[T], Var[T |*| Y] |*| Var[A1 |*| A2]]] =
          varIsNotPair(ev.flip)

        override def asZip[P1, P2](using
          ev: (Var[A1] |*| Var[A2]) =:= (P1 |*| P2),
        ): Exists[[V1] =>> Exists[[V2] =>> (Zip[V1, V2], P1 =:= Var[V1], P2 =:= Var[V2], Var[A1 |*| A2] =:= Var[V1 |*| V2])]] =
          ev match
            case BiInjective[|*|](ev1 @ TypeEq(Refl()), ev2 @ TypeEq(Refl())) =>
              Exists(Exists(this, ev1, ev2, summon))
      }

      case class Map[A, B](f: A -⚬ B, resultVar: Var[B]) extends Op.Linear[Var[A], Var[B]] {
        override def terminalVars(a: Varz[Var[A]]): Varz[Var[B]] =
          Varz.atom(resultVar)

        override def outNLOps(a: NLOpss[Var[A]]): NLOpss[Var[B]] =
          NLOpss(NLOps(None, None, resultVar))

        override def gcdSimple[X, C](that: Op.Affine[Var[X], C])(using Var[A] =:= Var[X]): Option[Tail[Var[A], Var[B] |*| C]] =
          that match
            case Map(_, v) =>
              (testEqual(v, resultVar)) match
                case Some(TypeEq(Refl())) => Some(shOp.lift(this) > shOp.lift(DupVar()))
                case None                 => None
            case _ =>
              None

        override def prj1_gcd_this[A1, A2](that: Prj1[A1, A2])(using ev: Var[A] =:= Var[A1 |*| A2]): Option[Tail[Var[A1 |*| A2], Var[A1] |*| Var[B]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.prj1_gcd_this")

        override def prj2_gcd_this[A1, A2](that: Prj2[A1, A2])(using ev: Var[A] =:= Var[A1 |*| A2]): Option[Tail[Var[A1 |*| A2], Var[A2] |*| Var[B]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.prj2_gcd_this")

        override def unzip_gcd_this[T1, T2](that: Unzip[T1, T2])(using ev: Var[A] =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], (Var[T1] |*| Var[T2]) |*| Var[B]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.unzip_gcd_this")

        override def cap1_gcd_this[T, X](that: CaptureFst[T, X])(using Var[A] =:= Var[T]): Option[Tail[Var[T], Var[X |*| T] |*| Var[B]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.cap1_gcd_this")

        override def cap2_gcd_this[T, Y](that: CaptureSnd[T, Y])(using Var[A] =:= Var[T]): Option[Tail[Var[T], Var[T |*| Y] |*| Var[B]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.cap2_gcd_this")

        override def asZip[P1, P2](using ev: Var[A] =:= (P1 |*| P2)): Exists[[V1] =>> Exists[[V2] =>> (Zip[V1, V2], P1 =:= Var[V1], P2 =:= Var[V2], Var[B] =:= Var[V1 |*| V2])]] =
          varIsNotPair(ev)
      }

      case class NLOps[A](
        split: Option[A -⚬ (A |*| A)],
        discard: Option[[B] => Unit => (A |*| B) -⚬ B],
        resultVar: Var[A],
      ) extends Op.Linear[Var[A], Var[A]] {
        override def terminalVars(a: Varz[Var[A]]): Varz[Var[A]] =
          Varz.atom(resultVar)

        override def outNLOps(a: NLOpss[Var[A]]): NLOpss[Var[A]] =
          NLOpss(NLOps(None, None, resultVar))

        override def gcdSimple[X, C](that: Op.Affine[Var[X], C])(using Var[A] =:= Var[X]): Option[Tail[Var[A], Var[A] |*| C]] =
          that match
            case NLOps(_, _, v) =>
              (testEqual(v, resultVar)) match
                case Some(TypeEq(Refl())) => Some(shOp.lift(this) > shOp.lift(DupVar()))
                case None                 => None
            case _ =>
              None

        override def prj1_gcd_this[A1, A2](that: Prj1[A1, A2])(using ev: Var[A] =:= Var[A1 |*| A2]): Option[Tail[Var[A1 |*| A2], Var[A1] |*| Var[A]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.prj1_gcd_this")

        override def prj2_gcd_this[A1, A2](that: Prj2[A1, A2])(using ev: Var[A] =:= Var[A1 |*| A2]): Option[Tail[Var[A1 |*| A2], Var[A2] |*| Var[A]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.prj2_gcd_this")

        override def unzip_gcd_this[T1, T2](that: Unzip[T1, T2])(using ev: Var[A] =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], (Var[T1] |*| Var[T2]) |*| Var[A]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.unzip_gcd_this")

        override def cap1_gcd_this[T, X](that: CaptureFst[T, X])(using Var[A] =:= Var[T]): Option[Tail[Var[T], Var[X |*| T] |*| Var[A]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.cap1_gcd_this")

        override def cap2_gcd_this[T, Y](that: CaptureSnd[T, Y])(using Var[A] =:= Var[T]): Option[Tail[Var[T], Var[T |*| Y] |*| Var[A]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.cap2_gcd_this")

        override def asZip[P1, P2](using ev: Var[A] =:= (P1 |*| P2)): Exists[[V1] =>> Exists[[V2] =>> (Zip[V1, V2], P1 =:= Var[V1], P2 =:= Var[V2], Var[A] =:= Var[V1 |*| V2])]] =
          varIsNotPair(ev)
      }

      case class Prj1[A1, A2](resultVar: Var[A1], unusedVar: Var[A2]) extends Affine[Var[A1 |*| A2], Var[A1]] {
        override def terminalVars(a: Varz[Var[A1 |*| A2]]): Varz[Var[A1]] =
          Varz.atom(resultVar)

        override def outNLOps(a: NLOpss[Var[A1 |*| A2]]): NLOpss[Var[A1]] =
          NLOpss(NLOps(None, None, resultVar))

        override def gcdSimple[X, C](that: Op.Affine[Var[X], C])(using ev: Var[A1 |*| A2] =:= Var[X]): Option[Tail[Var[A1 |*| A2], Var[A1] |*| C]] =
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
            case Injective[Var](BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl()))) =>
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

        override def cap1_gcd_this[T, X](that: CaptureFst[T, X])(using Var[A1 |*| A2] =:= Var[T]): Option[Tail[Var[T], Var[X |*| T] |*| Var[A1]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.cap1_gcd_this")

        override def cap2_gcd_this[T, Y](that: CaptureSnd[T, Y])(using Var[A1 |*| A2] =:= Var[T]): Option[Tail[Var[T], Var[T |*| Y] |*| Var[A1]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.cap2_gcd_this")

        override def asZip[P1, P2](using ev: Var[A1 |*| A2] =:= (P1 |*| P2)): Exists[[V1] =>> Exists[[V2] =>> (Zip[V1, V2], P1 =:= Var[V1], P2 =:= Var[V2], Var[A1] =:= Var[V1 |*| V2])]] =
          varIsNotPair(ev)
      }

      case class Prj2[A1, A2](unusedVar: Var[A1], resultVar: Var[A2]) extends Affine[Var[A1 |*| A2], Var[A2]] {
        override def terminalVars(a: Varz[Var[A1 |*| A2]]): Varz[Var[A2]] =
          Varz.atom(resultVar)

        override def outNLOps(a: NLOpss[Var[A1 |*| A2]]): NLOpss[Var[A2]] =
          NLOpss(NLOps(None, None, resultVar))

        override def gcdSimple[X, C](that: Op.Affine[Var[X], C])(using ev: Var[A1 |*| A2] =:= Var[X]): Option[Tail[Var[A1 |*| A2], Var[A2] |*| C]] =
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

        override def cap1_gcd_this[T, X](that: CaptureFst[T, X])(using Var[A1 |*| A2] =:= Var[T]): Option[Tail[Var[T], Var[X |*| T] |*| Var[A2]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.cap1_gcd_this")

        override def cap2_gcd_this[T, Y](that: CaptureSnd[T, Y])(using Var[A1 |*| A2] =:= Var[T]): Option[Tail[Var[T], Var[T |*| Y] |*| Var[A2]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.cap2_gcd_this")

        override def asZip[P1, P2](using ev: Var[A1 |*| A2] =:= (P1 |*| P2)): Exists[[V1] =>> Exists[[V2] =>> (Zip[V1, V2], P1 =:= Var[V1], P2 =:= Var[V2], Var[A2] =:= Var[V1 |*| V2])]] =
          varIsNotPair(ev)
      }

      case class Unzip[A1, A2](resultVar1: Var[A1], resultVar2: Var[A2]) extends Op.Linear[Var[A1 |*| A2], Var[A1] |*| Var[A2]] {
        override def terminalVars(a: Varz[Var[A1 |*| A2]]): Varz[Var[A1] |*| Var[A2]] =
          Varz.zip(Varz.atom(resultVar1), Varz.atom(resultVar2))

        override def outNLOps(a: NLOpss[Var[A1 |*| A2]]): NLOpss[Var[A1] |*| Var[A2]] =
          NLOpss(NLOps(None, None, resultVar1)) <*> NLOpss(NLOps(None, None, resultVar2))

        override def gcdSimple[X, C](that: Op.Affine[Var[X], C])(using ev: Var[A1 |*| A2] =:= Var[X]): Option[Tail[Var[A1 |*| A2], Var[A1] |*| Var[A2] |*| C]] =
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

        override def cap1_gcd_this[T, X](that: CaptureFst[T, X])(using Var[A1 |*| A2] =:= Var[T]): Option[Tail[Var[T], Var[X |*| T] |*| (Var[A1] |*| Var[A2])]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.cap1_gcd_this")

        override def cap2_gcd_this[T, Y](that: CaptureSnd[T, Y])(using Var[A1 |*| A2] =:= Var[T]): Option[Tail[Var[T], Var[T |*| Y] |*| (Var[A1] |*| Var[A2])]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.cap2_gcd_this")

        override def asZip[P1, P2](using ev: Var[A1 |*| A2] =:= (P1 |*| P2)): Exists[[V1] =>> Exists[[V2] =>> (Zip[V1, V2], P1 =:= Var[V1], P2 =:= Var[V2], (Var[A1] |*| Var[A2]) =:= Var[V1 |*| V2])]] =
          varIsNotPair(ev)
      }

      case class DupVar[A]() extends Op[Var[A], Var[A] |*| Var[A]] {
        override def terminalVars(a: Varz[Var[A]]): Varz[Var[A] |*| Var[A]] =
          Varz.zip(a, a)

        override def outNLOps(a: NLOpss[Var[A]]): NLOpss[Var[A] |*| Var[A]] =
          a <*> a
      }

      case class CaptureFst[A, X](x: Expr[X], resultVar: Var[X |*| A]) extends Op.Linear[Var[A], Var[X |*| A]] {
        override def terminalVars(a: Varz[Var[A]]): Varz[Var[X |*| A]] =
          Varz.atom(resultVar)

        override def outNLOps(a: NLOpss[Var[A]]): NLOpss[Var[X |*| A]] =
          NLOpss(NLOps(None, None, resultVar))

        override def gcdSimple[Q, C](that: Op.Affine[Var[Q], C])(using ev: Var[A] =:= Var[Q]): Option[Tail[Var[A], Var[X |*| A] |*| C]] =
          that.cap1_gcd_this(this)(using ev.flip)

        override def prj1_gcd_this[T1, T2](that: Prj1[T1, T2])(using ev: Var[A] =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], Var[T1] |*| Var[X |*| A]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.prj1_gcd_this")

        override def prj2_gcd_this[T1, T2](that: Prj2[T1, T2])(using ev: Var[A] =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], Var[T2] |*| Var[X |*| A]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.prj2_gcd_this")

        override def unzip_gcd_this[T1, T2](that: Unzip[T1, T2])(using ev: Var[A] =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], (Var[T1] |*| Var[T2]) |*| Var[X |*| A]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.unzip_gcd_this")

        override def cap1_gcd_this[T, Y](that: CaptureFst[T, Y])(using ev: Var[A] =:= Var[T]): Option[Tail[Var[T], Var[Y |*| T] |*| Var[X |*| A]]] =
          ev match { case Injective[Var](TypeEq(Refl())) =>
            testEqual(that.resultVar, this.resultVar) map {
              case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                shOp.lift(this) > shOp.lift(DupVar[X |*| A]())
            }
          }

        override def cap2_gcd_this[T, Y](that: CaptureSnd[T, Y])(using Var[A] =:= Var[T]): Option[Tail[Var[T], Var[T |*| Y] |*| Var[X |*| A]]] =
          None

        override def asZip[P1, P2](using ev: Var[A] =:= (P1 |*| P2)): Exists[[V1] =>> Exists[[V2] =>> (Zip[V1, V2], P1 =:= Var[V1], P2 =:= Var[V2], Var[X |*| A] =:= Var[V1 |*| V2])]] =
          varIsNotPair(ev)
      }

      case class CaptureSnd[A, X](x: Expr[X], resultVar: Var[A |*| X]) extends Op.Linear[Var[A], Var[A |*| X]] {
        override def terminalVars(a: Varz[Var[A]]): Varz[Var[A |*| X]] =
          Varz.atom(resultVar)

        override def outNLOps(a: NLOpss[Var[A]]): NLOpss[Var[A |*| X]] =
          NLOpss(NLOps(None, None, resultVar))

        override def gcdSimple[Q, C](that: Op.Affine[Var[Q], C])(using ev: Var[A] =:= Var[Q]): Option[Tail[Var[A], Var[A |*| X] |*| C]] =
          that.cap2_gcd_this(this)(using ev.flip)

        override def prj1_gcd_this[T1, T2](that: Prj1[T1, T2])(using ev: Var[A] =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], Var[T1] |*| Var[A |*| X]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.prj1_gcd_this")

        override def prj2_gcd_this[T1, T2](that: Prj2[T1, T2])(using ev: Var[A] =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], Var[T2] |*| Var[A |*| X]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.prj2_gcd_this")

        override def unzip_gcd_this[T1, T2](that: Unzip[T1, T2])(using ev: Var[A] =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], (Var[T1] |*| Var[T2]) |*| Var[A |*| X]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.unzip_gcd_this")

        override def cap1_gcd_this[T, Y](that: CaptureFst[T, Y])(using Var[A] =:= Var[T]): Option[Tail[Var[T], Var[Y |*| T] |*| Var[A |*| X]]] =
          None

        override def cap2_gcd_this[T, Y](that: CaptureSnd[T, Y])(using ev: Var[A] =:= Var[T]): Option[Tail[Var[T], Var[T |*| Y] |*| Var[A |*| X]]] =
          ev match { case Injective[Var](TypeEq(Refl())) =>
            testEqual(that.resultVar, this.resultVar) map {
              case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                shOp.lift(this) > shOp.lift(DupVar())
            }
          }

        override def asZip[P1, P2](using ev: Var[A] =:= (P1 |*| P2)): Exists[[V1] =>> Exists[[V2] =>> (Zip[V1, V2], P1 =:= Var[V1], P2 =:= Var[V2], Var[A |*| X] =:= Var[V1 |*| V2])]] =
          varIsNotPair(ev)
      }

      val project: [t, u, v] => (op: Op[t, u], p: Projection[|*|, u, v]) => shOp.ProjectRes[t, v] =
        [t, u, v] => (op: Op[t, u], p: Projection[|*|, u, v]) => op.project(p)

      /** Focuses on _some_ input variable of an operation. */
      sealed trait InputVarFocus[A, B] {
        type F[_]
        type X
        val F: Focus[|*|, F]
        val ev: A =:= F[Var[X]]
        val op: Op.Affine[F[Var[X]], B]
      }

      object InputVarFocus {
        def apply[G[_], T, B](op0: Op.Affine[G[Var[T]], B], g: Focus[|*|, G]): InputVarFocus[G[Var[T]], B] =
          new InputVarFocus[G[Var[T]], B] {
            override type F[A] = G[A]
            override type X = T
            override val F = g
            override val ev = summon
            override val op = op0
          }

        def apply[A, B](op: Op.Affine[A, B]): InputVarFocus[A, B] =
          op match {
            case op: Zip[t, u]        => InputVarFocus[[x] =>> x |*| Var[u], t, Var[t |*| u]](op, Focus.fst) // arbitrarily picking the first input
            case op: Unzip[t, u]      => InputVarFocus[[x] =>> x, t |*| u, Var[t] |*| Var[u]](op, Focus.id)
            case op: Prj1[t, u]       => InputVarFocus[[x] =>> x, t |*| u, Var[t]](op, Focus.id)
            case op: Prj2[t, u]       => InputVarFocus[[x] =>> x, t |*| u, Var[u]](op, Focus.id)
            case op: Map[t, u]        => InputVarFocus[[x] =>> x, t, Var[u]](op, Focus.id)
            case op: CaptureFst[t, u] => InputVarFocus[[x] =>> x, t, Var[u |*| t]](op, Focus.id)
            case op: CaptureSnd[t, u] => InputVarFocus[[x] =>> x, t, Var[t |*| u]](op, Focus.id)
            case op: NLOps[t]         => InputVarFocus[[x] =>> x, t, Var[t]](op, Focus.id)
          }
      }

      def gcd[C[_], D[_], X, Y, Z](
        f: Op.Affine[C[Var[X]], Y],
        g: Op.Affine[D[Var[X]], Z],
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
            None
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

    type Varz[A] = Bin[|*|, Var, Var, A]
    object Varz {
      def atom[A](a: Var[A]): Varz[Var[A]] =
        Bin.Leaf(a)

      def zip[A, B](a: Varz[A], b: Varz[B]): Varz[A |*| B] =
        Bin.Branch(a, b)
    }

    val shOp = Shuffled[Op, |*|](shuffled.shuffle)
    import shOp.shuffle.{zip => zipEq}

    type VarOp[A, B] = (Varz[A], Op[A, B])
    given shVOp: Shuffled.With[VarOp, |*|, shuffled.shuffle.type] =
      Shuffled[VarOp, |*|](shuffled.shuffle)

    type NLOpss[A] = Bin[|*|, Var, Op.NLOps, A]
    object NLOpss {
      def apply[A](op: Op.NLOps[A]): NLOpss[Var[A]] =
        Bin.Leaf(op)
    }
    type NLOpsOp[A, B] = (NLOpss[A], Op[A, B])
    given shNLOp: Shuffled.With[NLOpsOp, |*|, shuffled.shuffle.type] =
      Shuffled[NLOpsOp, |*|](shuffled.shuffle)

    given shLOp: Shuffled.With[Op.Linear, |*|, shuffled.shuffle.type] =
      Shuffled[Op.Linear, |*|](shuffled.shuffle)

    enum CaptureOp[A, B] {
      case Id[A]() extends CaptureOp[A, A]
      case CaptureFst[X, A](captured: Expr[X]) extends CaptureOp[A, X |*| A]
      case CaptureSnd[A, X](captured: Expr[X]) extends CaptureOp[A, A |*| X]
    }

    type Tail[A, B] =
      shOp.Shuffled[A, B]

    type VTail[A, B] =
      shVOp.Shuffled[A, B]

    type NLTail[A, B] =
      shNLOp.Shuffled[A, B]

    type LTail[A, B] =
      shLOp.Shuffled[A, B]

    def id[A](v: Var[A]): HybridArrow[A, Var[A]] =
      HybridArrow(v, shOp.id)

    def dupVar[A]: Tail[Var[A], Var[A] |*| Var[A]] =
      shOp.lift(Op.DupVar())

    def map[A, B](f: A -⚬ B, resultVar: Var[B]): Tail[Var[A], Var[B]] =
      shOp.lift(Op.Map(f, resultVar))

    def nlOps[A](
      split: Option[A -⚬ (A |*| A)],
      discard: Option[[B] => Unit => (A |*| B) -⚬ B],
      resultVar: Var[A],
    ): Tail[Var[A], Var[A]] =
      shOp.lift(Op.NLOps(split, discard, resultVar))

    def captureFst[A, X](x: Expr[X], resultVar: Var[X |*| A]): Tail[Var[A], Var[X |*| A]] =
      shOp.lift(Op.CaptureFst(x, resultVar))

    def captureSnd[A, X](x: Expr[X], resultVar: Var[A |*| X]): Tail[Var[A], Var[A |*| X]] =
      shOp.lift(Op.CaptureSnd(x, resultVar))

    def zip[A1, A2](resultVar: Var[A1 |*| A2]): Tail[Var[A1] |*| Var[A2], Var[A1 |*| A2]] =
      shOp.lift(Op.Zip(resultVar))

    def prj1[A1, A2](resultVar: Var[A1], unusedVar: Var[A2]): Tail[Var[A1 |*| A2], Var[A1]] =
      shOp.lift(Op.Prj1(resultVar, unusedVar))

    def prj2[A1, A2](unusedVar: Var[A1], resultVar: Var[A2]): Tail[Var[A1 |*| A2], Var[A2]] =
      shOp.lift(Op.Prj2(unusedVar, resultVar))

    /** If `op` introduces a new variable(s), searches through `t` for an existing occurrence of `op`
     *  and channels it to the output.
     *  If `op` does not introduce new variables, or if `op` is not found in `t`, returns `None`.
     */
    def pullOut[A, G[_], X, D[_], Y](t: Tail[A, G[Var[X]]], op: Op.Affine[D[Var[X]], Y])(
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
      op: Op.Affine[D[Var[X]], Y],
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
            pullBumpDupVar[A, F, v0, C, G[Var[v0]], D, Y](pre, post, op)(F, C, D)(using
              ev1,
            )
          }
        case Op.Zip(_)           => None
        case Op.CaptureFst(_, _) => None
        case Op.CaptureSnd(_, _) => None
        case Op.Unzip(_, _)      => None
        case Op.Map(_, _)        => None
        case Op.Prj1(_, _)       => None
        case Op.Prj2(_, _)       => None
        case Op.NLOps(_, _, _)   => None
    }

    def pullBumpDupVar[A, F[_], V, C[_], B, D[_], Y](
      pre: Tail[A, F[Var[V]]],
      post: Tail[F[C[Var[V]]], B],
      op: Op.Affine[D[Var[V]], Y],
    )(
      F: Focus[|*|, F],
      C: Focus[|*|, C],
      D: Focus[|*|, D],
    )(using
      ev: C[Var[V]] =:= (Var[V] |*| Var[V]),
    ): Option[Tail[A, B |*| Y]] = ev match { case TypeEq(Refl()) =>
      C match
        case c: Focus.Fst[pair, c1, q] =>
          (summon[(c1[Var[V]] |*| q) =:= C[Var[V]]] andThen ev) match { case BiInjective[|*|](c1vv_vv @ TypeEq(Refl()), q_vv @ TypeEq(Refl())) =>
            c.i match
              case Focus.Id() =>
                (summon[Var[V] =:= c1[Var[V]]] andThen c1vv_vv) match
                  case TypeEq(Refl()) =>
                    pullBumpDupVarChaseOther[A, F, V, [x] =>> Var[V] |*| x, B, D, Y](pre, post, op)(F, Focus.snd[|*|, Var[V]], D)
              case _: Focus.Fst[pair, c11, p] =>
                varIsNotPair(c1vv_vv.flip andThen summon[c1[Var[V]] =:= (c11[Var[V]] |*| p)])
              case _: Focus.Snd[pair, c12, p] =>
                varIsNotPair(c1vv_vv.flip andThen summon[c1[Var[V]] =:= (p |*| c12[Var[V]])])
          }
        case c: Focus.Snd[pair, c2, p] =>
          (summon[(p |*| c2[Var[V]]) =:= C[Var[V]]] andThen ev) match { case BiInjective[|*|](TypeEq(Refl()), c2vv_vv @ TypeEq(Refl())) =>
            c.i match
              case Focus.Id() =>
                (summon[Var[V] =:= c2[Var[V]]] andThen c2vv_vv) match
                  case TypeEq(Refl()) =>
                    pullBumpDupVarChaseOther[A, F, V, [x] =>> x |*| Var[V], B, D, Y](pre, post, op)(F, Focus.fst[|*|, Var[V]], D)
              case _: Focus.Fst[pair, c21, q] =>
                varIsNotPair(c2vv_vv.flip andThen summon[c2[Var[V]] =:= (c21[Var[V]] |*| q)])
              case _: Focus.Snd[pair, c22, q] =>
                varIsNotPair(c2vv_vv.flip andThen summon[c2[Var[V]] =:= (q |*| c22[Var[V]])])
          }
        case Focus.Id() =>
          varIsNotPair(summon[Var[V] =:= (Var[V] |*| Var[V])])
    }

    /** After bumping into one output of DupVar. */
    private def pullBumpDupVarChaseOther[A, F[_], V, O[_], B, D[_], Y](
      pre: Tail[A, F[Var[V]]],
      post: Tail[F[O[Var[V]]], B],
      op: Op.Affine[D[Var[V]], Y],
    )(
      F: Focus[|*|, F],
      O: Focus[|*|, O],
      D: Focus[|*|, D],
    )(using
      ev: O[Var[V]] =:= (Var[V] |*| Var[V]),
    ): Option[Tail[A, B |*| Y]] =
      // chase forward through the other output of DupVar
      pushOut[[x] =>> F[O[x]], V, D, Y, B](post, op)(F compose O, D) match
        case Some(post1) =>
          Some(pre > shOp.lift(Op.DupVar[V]()).to(using ev.flip).at(F) > post1)
        case None =>
          // chase upstream
          pullOut[A, F, V, D, Y](pre, op)(F, D) match
            case Some(pre1) =>
              val post1: Tail[F[Var[V]], B] =
                shOp.lift(Op.DupVar[V]()).to(using ev.flip).at(F) > post
              Some(pre1 > shOp.extractSnd(F) > post1.inFst)
            case None =>
              None

    def pushOut[F[_], X, D[_], Y, B](t: Tail[F[Var[X]], B], op: Op.Affine[D[Var[X]], Y])(
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
      op: Op.Affine[D[Var[X]], Y],
    )(
      C: Focus[|*|, C],
      G: Focus[|*|, G],
      D: Focus[|*|, D],
    ): Option[Tail[A, B |*| Y]] =
      obstacle.maskInput.visit([CX] => (o: Op[CX, W], ev: CX =:= C[Var[X]]) => {
        o match
          case o: Op.DupVar[v0] =>
            summon[W =:= (Var[v0] |*| Var[v0])]
            given ev1: (C[Var[X]] =:= Var[v0]) = ev.flip andThen summon[CX =:= Var[v0]]
            given evx: (Var[X] =:= Var[v0]) = C.mustBeId[Var[X], v0]
            def go[E[_]](e: Focus[|*|, E])(using ev2: W =:= E[Var[v0]]): Option[Tail[A, B |*| Y]] =
              ev1 match { case TypeEq(Refl()) =>
                evx match { case TypeEq(Refl()) =>
                  pushOut[[x] =>> G[E[x]], v0, D, Y, B](post.from(using ev2.flip.liftCo[G]), op.from(using evx.flip.liftCo[D]))(G compose e, D)
                    .map { post1 => pre.to[G[Var[v0]]](using ev1.liftCo[G]) > shOp.lift(Op.DupVar[v0]()).at(G) > post1.from(using ev2.liftCo[G]) }
                }
              }
            go[[x] =>> x |*| Var[v0]](Focus.fst) orElse go[[x] =>> Var[v0] |*| x](Focus.snd)
          case o: Op.Affine[cx, w] =>
            Op.gcd(o.from(using ev.flip), op)(C, D)
              .map { (res0: Tail[C[Var[X]], W |*| Y]) =>
                pre > res0.at(G) > shOp.extractSnd[G, W, Y](G) > post.inFst[Y]
              }
      })

    def discardFst[A, G[_], X, Y](t: Tail[Var[A], G[X |*| Y]], g: Focus[|*|, G]): Tail[Var[A], G[Y]] = {
      val prj: Projection[|*|, G[X |*| Y], G[Y]] = Projection.discardFst[|*|, X, Y].at[G](g)
      t.project(prj, Op.project) match
        case shOp.ProjectRes.Projected(p, f) =>
          p match
            case Projection.Id() =>
              f
            case p: Projection.Proper[pair, p, q] =>
              p.startsFromPair match
                case Exists.Some(Exists.Some(ev)) =>
                  varIsNotPair(ev)
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

    def extract[A, B, X, Y](a: NLOpss[A], t: Tail[A, B])(u: Unvar[A, X], v: Unvar[B, Y]): LinearRes[X, Y] = {
      val t1: NLTail[A, B] =
        t.sweepL[NLOpss, NLOpsOp](
          a,
          [p, q] => (p: NLOpss[p], op: Op[p, q]) => {
            val q = op.outNLOps(p)
            ((p, op), q)
          }
        )._1

      type Arr[T, U] = LinCheck[CapturingFun[T, U]]
      given shArr: Shuffled.With[Arr, |*|, shuffled.shuffle.type] =
        Shuffled[Arr, |*|](shuffled.shuffle)

      val t2: shArr.Shuffled[X, Y] =
        t1.translate[Arr, |*|, Unvar, X](
          u,
          Unvar.objectMap,
          new ArrowMap[NLOpsOp, Arr, Unvar] {
            import Unvar.{Par, SingleVar}
            override def map[A, B](op: NLOpsOp[A, B]): Image[A, B] =
              op match {
                case (opss, _: Op.Zip[a1, a2]) =>
                  Image(Par(SingleVar[a1](), SingleVar[a2]()), LinCheck.Success(CapturingFun.id), SingleVar[a1 |*| a2]())
                case (opss, op: Op.Map[a, b]) =>
                  Image(SingleVar[a](), LinCheck.Success(CapturingFun.lift(op.f)), SingleVar[b]())
                case (opss, _: Op.Unzip[a1, a2]) =>
                  Image(SingleVar[a1 |*| a2](), LinCheck.Success(CapturingFun.id), Par(SingleVar[a1](), SingleVar[a2]()))
                case (opss, op: Op.CaptureFst[a, x]) =>
                  Image(SingleVar[a](), LinCheck.Success(CapturingFun.captureFst(op.x)), SingleVar[x |*| a]())
                case (opss, op: Op.CaptureSnd[a, x]) =>
                  Image(SingleVar[a](), LinCheck.Success(CapturingFun.captureSnd(op.x)), SingleVar[a |*| x]())
                case (opss, op: Op.NLOps[a]) =>
                  Image(SingleVar[a](), LinCheck.Success(CapturingFun.id), SingleVar[a]())
                case (opss, op: Op.DupVar[a]) =>
                  val ops = opss.getValue[a]
                  Image(
                    SingleVar[a](),
                    ops.split match
                      case Some(split) => LinCheck.Success(CapturingFun.lift(split))
                      case None        => LinCheck.Failure(errors.overusedVars(variables.singleton(ops.resultVar))),
                    Par(SingleVar[a](), SingleVar[a]()),
                  )
                case (opss, op: Op.Prj1[a1, a2]) =>
                  Image(
                    SingleVar[a1 |*| a2](),
                    LinCheck.Failure(errors.underusedVars(variables.singleton(op.unusedVar))),
                    SingleVar[a1](),
                  )
                case (opss, op: Op.Prj2[a1, a2]) =>
                  Image(
                    SingleVar[a1 |*| a2](),
                    LinCheck.Failure(errors.underusedVars(variables.singleton(op.unusedVar))),
                    SingleVar[a2](),
                  )
                case (opss, other) =>
                  UnhandledCase.raise(s"$other")
              }
          },
        ) match {
          case Exists.Some((t2, v2)) =>
            (v uniqueOutType v2) match {
              case TypeEq(Refl()) =>
                t2
            }
        }

      given shCFun: Shuffled.With[CapturingFun, |*|, shuffled.shuffle.type] =
        Shuffled[CapturingFun, |*|](shuffled.shuffle)

      t2.traverse[LinCheck, CapturingFun](
        [p, q] => (op: LinCheck[CapturingFun[p, q]]) => op
      ) match {
        case LinCheck.Success(t3) =>
          t3.fold match {
            case ll.CapturingFun.NoCapture(f)  => LinearRes.Exact(f)
            case ll.CapturingFun.Closure(x, f) => LinearRes.Closure(x, f)
          }
        case LinCheck.Failure(e) =>
          LinearRes.Violation(e)
      }
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
        case op: Op.Linear[a, b] =>
          LinCheck.Success(op)
        case op: Op.DupVar[a] =>
          val v = vs.getValue[a]
          LinCheck.Failure(errors.overusedVars(variables.singleton(v)))
        case p: Op.Prj1[a1, a2] =>
          LinCheck.Failure(errors.underusedVars(variables.singleton(p.unusedVar)))
        case p: Op.Prj2[a1, a2] =>
          LinCheck.Failure(errors.underusedVars(variables.singleton(p.unusedVar)))
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
                (summon[Var[v] =:= VV] andThen ev) match { case Injective[Var](TypeEq(Refl())) =>
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
            Varz.atom(va)
          case Multiplier.Dup(m1, m2) =>
            Varz.zip(multiply(m1), multiply(m2))
        }
    }
  }

  private given varIsNotPair: ([V, A, B] => (Var[V] =:= (A |*| B)) => Nothing) =
    [V, A, B] => (ev: Var[V] =:= (A |*| B)) => throw new AssertionError("Var[A] =:= (A |*| B)")

  private given nlOpsIsNotPair: ([V, A, B] => (HybridArrow.Op.NLOps[V] =:= (A |*| B)) => Nothing) =
    [V, A, B] => (ev: HybridArrow.Op.NLOps[V] =:= (A |*| B)) => throw new AssertionError("Var[A] =:= (A |*| B)")

  extension[F[_], V, U](ev: F[Var[V]] =:= (Var[U] |*| Var[U])) {
    def deriveEquality(f: Focus[|*|, F]): V =:= U =
      f match {
        case f: Focus.Fst[pair, f1, q] =>
          (summon[(f1[Var[V]] |*| q) =:= F[Var[V]]] andThen ev) match { case BiInjective[|*|](f1v_u @ TypeEq(Refl()), TypeEq(Refl())) =>
            f.i match
              case Focus.Id() =>
                (summon[Var[V] =:= f1[Var[V]]] andThen f1v_u) match
                  case Injective[Var](v_u) => v_u
              case _: Focus.Fst[pair, g1, t] =>
                varIsNotPair(f1v_u.flip andThen summon[f1[Var[V]] =:= (g1[Var[V]] |*| t)])
              case _: Focus.Snd[pair, g2, s] =>
                varIsNotPair(f1v_u.flip andThen summon[f1[Var[V]] =:= (s |*| g2[Var[V]])])
          }
        case f: Focus.Snd[pair, f2, p] =>
          (summon[(p|*| f2[Var[V]]) =:= F[Var[V]]] andThen ev) match { case BiInjective[|*|](TypeEq(Refl()), f2v_u @ TypeEq(Refl())) =>
            f.i match
              case Focus.Id() =>
                (summon[Var[V] =:= f2[Var[V]]] andThen f2v_u) match
                  case Injective[Var](v_u) => v_u
              case _: Focus.Fst[pair, g1, t] =>
                varIsNotPair(f2v_u.flip andThen summon[f2[Var[V]] =:= (g1[Var[V]] |*| t)])
              case _: Focus.Snd[pair, g2, s] =>
                varIsNotPair(f2v_u.flip andThen summon[f2[Var[V]] =:= (s |*| g2[Var[V]])])
          }
        case Focus.Id() =>
          varIsNotPair(ev)
      }
  }

  extension [F[_]](f: Focus[|*|, F]) {
    def mustBeId[A, V](using ev: F[A] =:= Var[V]): A =:= Var[V] =
      f match
        case Focus.Id()                => ev
        case _: Focus.Fst[pair, f1, y] => varIsNotPair(ev.flip)
        case _: Focus.Snd[pair, f2, x] => varIsNotPair(ev.flip)
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