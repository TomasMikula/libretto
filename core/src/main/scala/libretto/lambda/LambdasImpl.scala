package libretto.lambda

import libretto.{lambda => ll}
import libretto.lambda.Lambdas.Error.LinearityViolation
import libretto.lambda.Lambdas.ErrorFactory
import libretto.util.{Applicative, BiInjective, Exists, Injective, Masked, TypeEq, UniqueTypeArg}
import libretto.util.TypeEq.Refl
import scala.annotation.{tailrec, targetName}

class LambdasImpl[-⚬[_, _], |*|[_, _], V, E, LE](using
  ssc: SymmetricSemigroupalCategory[-⚬, |*|],
  inj: BiInjective[|*|],
  errors: ErrorFactory[E, LE, V],
) extends Lambdas[-⚬, |*|, V, E, LE] {

  given shuffle: Shuffle[|*|] = Shuffle[|*|]
  given shuffled: Shuffled.With[-⚬, |*|, shuffle.type] = Shuffled[-⚬, |*|](shuffle)
  import shuffled.shuffle.{~⚬, Transfer, TransferOpt}
  import shuffled.{Shuffled => ≈⚬, assocLR, assocRL, fst, id, ix, ixi, lift, par, pure, snd, swap, xi}

  override type AbstractFun[A, B] =
    A ≈⚬ B

  override object AbstractFun extends AbstractFuns {
    override def fold[A, B](f: AbstractFun[A, B]): A -⚬ B =
      f.fold
  }

  type Var[A] = libretto.lambda.Var[V, A]

  override opaque type Context = ContextImpl[-⚬, |*|, V]
  override object Context extends Contexts {
    override def fresh(): Context =
      new ContextImpl[-⚬, |*|, V]

    override def nested(parent: Context): Context =
      new ContextImpl[-⚬, |*|, V](Some(parent))

    override def newVar[A](label: V)(using ctx: Context): Var[A] =
      ctx.newVar[A](label)

    override def registerNonLinearOps[A](v: Var[A])(
      split: Option[A -⚬ (A |*| A)],
      discard: Option[[B] => Unit => (A |*| B) -⚬ B],
    )(using ctx: Context): Unit =
      ctx.register(v)(split, discard)

    override def registerConstant[A](v: Var[A])(
      introduce: [x] => Unit => x -⚬ (A |*| x),
    )(using ctx: Context): Unit =
      ctx.registerConstant(v)(introduce)

    override def getSplit[A](v: Var[A])(using ctx: Context): Option[A -⚬ (A |*| A)] =
      ctx.getSplit(v)

    override def getDiscard[A](v: Var[A])(using ctx: Context): Option[[B] => Unit => (A |*| B) -⚬ B] =
      ctx.getDiscard(v)

    override def getConstant[A](v: Var[A])(using ctx: Context): Option[[x] => Unit => x -⚬ (A |*| x)] =
      ctx.getConstant(v)
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
      ll.CapturingFun.Closure(ll.Tupled.atom(captured), shuffled.id)

    def captureSnd[X, A](captured: Expr[X]): CapturingFun[A, A |*| X] =
      ll.CapturingFun.Closure(ll.Tupled.atom(captured), shuffled.swap)
  }

  /**
   * AST of an expression, created by user code, before translation to point-free representation,
   * containing intermediate [[Var]]s.
   * Non-linear: includes projections and multiple occurrences of the same variable.
   */
  sealed trait Expr[B] {
    import Expr._

    def resultVar: Var[B]

    def initialVars: Var.Set[V] =
      this match {
        case Id(a)         => Var.Set(a)
        case Map(f, _, _)  => f.initialVars
        case Zip(f, g, _)  => f.initialVars merge g.initialVars
        case Prj1(f, _, _) => f.initialVars
        case Prj2(f, _, _) => f.initialVars
      }

    def map[C](f: B -⚬ C)(resultVar: Var[C]): Expr[C] =
      Map(this, f, resultVar)

    def zip[D](that: Expr[D])(resultVar: Var[B |*| D]): Expr[B |*| D] =
      Zip(this, that, resultVar)

    /** Goes from the end backwards (i.e. from the result variable towards inital variables)
     * and splits this expression at the boundary where the given predicate first returns `true`.
     * Initial variables of the resulting trimmed `Expr[B]` (second part of the returned tuple)
     * are exactly the terminal variables of the returned prefix expressions (first part of the returned tuple).
     * If in some branch the predicate never returns `true`, the expression's initial variable in that branch is returned as `Left`.
     */
    def splitAt(p: [X] => Var[X] => Boolean): Exists[[x] =>> (Tupled[[t] =>> Either[Var[t], Expr[t]], x], Expr[B])] =
      if (p(resultVar)) {
        Exists((Tupled.atom(Right(this)), Id(resultVar)))
      } else {
        this match {
          case Id(v) =>
            Exists((Tupled.atom(Left(v)), Id(v)))
          case Map(y, f, v) =>
            y.splitAt(p) match
              case Exists.Some((x, y)) =>
                Exists((x, Map(y, f, v)))
          case Zip(y1, y2, v) =>
            (y1.splitAt(p), y2.splitAt(p)) match
              case (Exists.Some((x1, y1)), Exists.Some((x2, y2))) =>
                Exists((x1 zip x2), Zip(y1, y2, v))
          case Prj1(y, v1, v2) =>
            y.splitAt(p) match
              case Exists.Some((x, y)) =>
                Exists.Some((x, Prj1(y, v1, v2)))
          case Prj2(y, v1, v2) =>
            y.splitAt(p) match
              case Exists.Some((x, y)) =>
                Exists.Some((x, Prj2(y, v1, v2)))
        }
      }
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

    override def variable[A](a: Var[A]): Expr[A] =
      Id(a)

    override def map[B, C](f: Expr[B], g: B -⚬ C, resultVar: V)(using Context): Expr[C] =
      (f map g)(Context.newVar(resultVar))

    override def zip[B1, B2](f1: Expr[B1], f2: Expr[B2], resultVar: V)(using Context): Expr[B1 |*| B2] =
      (f1 zip f2)(Context.newVar(resultVar))

    override def unzip0[B1, B2](f: Expr[B1 |*| B2])(v1: Var[B1], v2: Var[B2]): (Expr[B1], Expr[B2]) =
      (Prj1(f, v1, v2), Prj2(f, v1, v2))

    override def unzip[B1, B2](f: Expr[B1 |*| B2])(resultVar1: V, resultVar2: V)(using Context): (Expr[B1], Expr[B2]) = {
      val v1 = Context.newVar[B1](resultVar1)
      val v2 = Context.newVar[B2](resultVar2)
      unzip0(f)(v1, v2)
    }

    override def const[A](introduce: [x] => Unit => x -⚬ (A |*| x))(varName: V)(using Context): Expr[A] = {
      val v = Context.newVar[A](varName)
      Context.registerConstant(v)(introduce)
      Id(v)
    }

    override def resultVar[B](f: Expr[B]): Var[B] =
      f.resultVar

    override def initialVars[B](f: Expr[B]): Var.Set[V] =
      f.initialVars

    def splitAt[B](b: Tupled[Expr, B])(p: [X] => Var[X] => Boolean): Exists[[x] =>> (Tupled[[t] =>> Either[Var[t], Expr[t]], x], Tupled[Expr, B])] =
      b.asBin match {
        case Bin.Leaf(b) =>
          b.splitAt(p) match
            case Exists.Some((x, b)) =>
              Exists((x, Tupled.atom(b)))
        case Bin.Branch(l, r) =>
          ( splitAt(Tupled.fromBin(l))(p)
          , splitAt(Tupled.fromBin(r))(p)
          ) match
            case (Exists.Some((x, b1)), Exists.Some((y, b2))) =>
              Exists((x zip y, b1 zip b2))
      }
  }

  override def eliminateVariable[A, B](boundVar: Var[A], expr: Expr[B])(using Context): Abstracted[A, B] =
    eliminateVariableN(boundVar, Tupled.atom(expr))

  def eliminateVariableN[A, B](boundVar: Var[A], exprs: Tupled[Expr, B])(using Context): Abstracted[A, B] = {
    import Lambdas.Abstracted.{Closure, Exact, Failure}

    eliminateVarN(boundVar, exprs) match {
      case Right(res) =>
        res match {
          // case Closure(x, f) =>
            // eliminate all constant expressions

            // split at constants

            // eliminate constants from capture

            // type Intro[T] = [x] => Unit => x -⚬ (T |*| x)
            // val y = x.asBin
            // given shuffled.shuffle.type = shuffled.shuffle
            // y.partition[Expr, Intro](
            //   [t] => (t: Expr[t]) =>
            //     Context.getConstant(t.resultVar) match {
            //       case Some(intro) => Right(intro)
            //       case None        => Left(t)
            //     }
            // ) match {
            //   case y.Partitioned.Left(y) =>
            //     Closure(Tupled.fromBin(y), f)
            //   case y.Partitioned.Right(y) =>

            // }
          case other =>
            other
        }
      case Left(EliminateRes.NotFound()) =>
        Failure(errors.underusedVar(boundVar))
    }
  }

  private def eliminateVarN[A, B](boundVar: Var[A], exprs: Tupled[Expr, B])(using Context): Either[EliminateRes.NotFound[A, B], Abstracted[A, B]] = {
    import Lambdas.Abstracted.{Closure, Exact, Failure}
    import EliminateRes.NotFound
    import libretto.lambda.{CapturingFun => cf}

    exprs.asBin match {
      case Bin.Leaf(b) =>
        eliminateVar(boundVar, b)
      case br: Bin.Branch[br, lf, f, b1, b2] =>
        val b1 = Tupled.fromBin(br.l)
        val b2 = Tupled.fromBin(br.r)
        ( eliminateVarN(boundVar, b1)
        , eliminateVarN(boundVar, b2)
        ) match {
          case (Right(r1), Right(r2)) =>
            Right(
              (r1.toEither, r2.toEither) match {
                case (Right(f1), Right(f2)) =>
                    Context.getSplit(boundVar) match
                      case Some(split) =>
                        (f1, f2) match
                          case (cf.NoCapture(f1), cf.NoCapture(f2)) =>
                            Exact(lift(split) > par(f1, f2))
                          case (cf.NoCapture(f1), cf.Closure(y, f2)) =>
                            Closure(y, snd(lift(split)) > xi > par(f1, f2))
                          case (cf.Closure(x, f1), cf.NoCapture(f2)) =>
                            Closure(x, snd(lift(split)) > assocRL > par(f1, f2))
                          case (cf.Closure(x, f1), cf.Closure(y, f2)) =>
                            Closure(x zip y, snd(lift(split)) > ixi > par(f1, f2))
                      case None =>
                        Failure(errors.overusedVar(boundVar))
                case (Left(e1), Left(e2)) =>
                  Failure(errors.combineLinear(e1, e2))
                case (Left(e1), _) =>
                  Failure(e1)
                case (_, Left(e2)) =>
                  Failure(e2)
              }
            )
          case (Right(r1), Left(NotFound())) =>
            Right(
              r1.toEither match
                case Right(f1) =>
                  f1 match
                    case cf.NoCapture(f1)  => Closure(b2, swap > fst(f1))
                    case cf.Closure(x, f1) => Closure(x zip b2, ix > fst(f1))
                case Left(e) =>
                  Failure(e)
            )
          case (Left(NotFound()), Right(r2)) =>
            Right(
              r2.toEither match
                case Right(f2) =>
                  f2 match
                    case cf.NoCapture(f2)  => Closure(b1, snd(f2))
                    case cf.Closure(y, f2) => Closure(b1 zip y, assocLR > snd(f2))
                case Left(e) =>
                  Failure(e)
            )
          case (Left(NotFound()), Left(NotFound())) =>
            Left(NotFound())
        }
    }
  }

  private def eliminateVar[A, B](boundVar: Var[A], expr: Expr[B])(using Context): Either[EliminateRes.NotFound[A, B], Abstracted[A, B]] = {
    import HybridArrow.{LinearRes, Op, Unvar, Varz}
    import Lambdas.Abstracted.{Closure, Exact, Failure}

    eliminate(boundVar, expr) match {
      case EliminateRes.Found(arr) =>
        Right(
          arr.extract(Unvar.SingleVar()) match {
            case LinearRes.Exact(f) =>
              Exact(f)
            case LinearRes.Closure(captured, g) =>
              deduplicateExpressions(captured) match
                case Right(Exists.Some((x, f1))) => Closure(x, f1.inFst[A] > g)
                case Left(e)                     => Failure(e)
            case LinearRes.Violation(e) =>
              Failure(e)
          }
        )
      case nf @ EliminateRes.NotFound() =>
        Left(nf)
    }
  }

  override def switch[<+>[_, _], A, B](
    cases: Sink[VFun, <+>, A, B],
    sum: [X, Y] => (X -⚬ B, Y -⚬ B) => (X <+> Y) -⚬ B,
    distribute: [X, Y, Z] => Unit => (X |*| (Y <+> Z)) -⚬ ((X |*| Y) <+> (X |*| Z))
  )(using
    Context,
  ): AbsRes[A, B] =
    switchImpl(cases, sum, distribute)

  private def deduplicateExpressions[AA](exprs: Tupled[Expr, AA])(using
    Context,
  ): Either[LE, Exists[[A] =>> (Tupled[Expr, A], AbstractFun[A, AA])]] = {
    enum Arr[A, B] {
      case FreeDup[A](expr: Expr[A]) extends Arr[A, A |*| A]
    }
    given Shuffled.With[Arr, |*|, shuffle.type] =
      Shuffled[Arr, |*|](shuffle)

    exprs.deduplicateLeafs[Arr](
      [x] => (x: Expr[x]) => Arr.FreeDup(x),
    ) match {
      case Exists.Some((a, f)) =>
        f.traverse[LinCheck, -⚬](
          [t, u] => (arr: Arr[t, u]) => {
            arr match
              case Arr.FreeDup(x) =>
                Context.getSplit(x.resultVar) match
                  case Some(split) => LinCheck.Success(split)
                  case None        => LinCheck.Failure(errors.overusedVars(Var.Set(x.resultVar)))
          },
        ) match {
          case LinCheck.Success(f) => Right(Exists((a, f)))
          case LinCheck.Failure(e) => Left(e)
        }
    }
  }

  private def bug(msg: String): Nothing =
    throw new AssertionError(msg)

  // Note: The variable is only searched for among initial variables of the expression,
  // not in any (intermediate) results.
  private def eliminate[A, B](v: Var[A], expr: Expr[B])(using Context): EliminateRes[A, B] = {
    import EliminateRes.{Found, NotFound}

    expr match
      case Expr.Id(w) =>
        (v testEqual w) match
          case Some(ev) =>
            Found(HybridArrow.id(v).to(using ev.liftCo[Var]))
          case None =>
            Context.getDiscard(v) match
              case Some(discardFst) => Found(HybridArrow(v, HybridArrow.captureReplace(discardFst, expr)))
              case None             => NotFound()
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
      assert((this.v testEqual that.v).isDefined)
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

    def extract[Y](u: Unvar[B, Y])(using
      Context,
    ): LinearRes[A, Y] = {
      val t1: VTail[Var[A], B] =
        tail.sweepL[Varz, VarOp](
          Varz.atom(v),
          [p, q] => (p: Varz[p], op: Op[p, q]) => {
            val q = op.terminalVars(p)
            ((p, op), q)
          }
        )._1

      type Arr[T, U] = LinCheck[CapturingFun[T, U]]
      given shArr: Shuffled.With[Arr, |*|, shuffled.shuffle.type] =
        Shuffled[Arr, |*|](shuffled.shuffle)

      val t2: shArr.Shuffled[A, Y] =
        t1.translate[Arr, |*|, Unvar, A](
          Unvar.SingleVar[A](),
          Unvar.objectMap,
          new ArrowMap[VarOp, Arr, Unvar] {
            import Unvar.{Par, SingleVar}
            override def map[A, B](op: VarOp[A, B]): Image[A, B] =
              op match {
                case (vars, _: Op.Zip[a1, a2]) =>
                  Image(Par(SingleVar[a1](), SingleVar[a2]()), LinCheck.Success(CapturingFun.id), SingleVar[a1 |*| a2]())
                case (vars, op: Op.Map[a, b]) =>
                  Image(SingleVar[a](), LinCheck.Success(CapturingFun.lift(op.f)), SingleVar[b]())
                case (vars, _: Op.Unzip[a1, a2]) =>
                  Image(SingleVar[a1 |*| a2](), LinCheck.Success(CapturingFun.id), Par(SingleVar[a1](), SingleVar[a2]()))
                case (vars, op: Op.CaptureFst[a, x]) =>
                  Image(SingleVar[a](), LinCheck.Success(CapturingFun.captureFst(op.x)), SingleVar[x |*| a]())
                case (vars, op: Op.CaptureSnd[a, x]) =>
                  Image(SingleVar[a](), LinCheck.Success(CapturingFun.captureSnd(op.x)), SingleVar[a |*| x]())
                case (vars, op: Op.CaptureReplace[a, b]) =>
                  Image(SingleVar[a](), LinCheck.Success(CapturingFun.captureSnd[b, a](op.replacement) > CapturingFun.lift(op.discard)), SingleVar[b]())
                case (vars, op: Op.DupVar[a]) =>
                  val v = vars.getValue[a]
                  Image(
                    SingleVar[a](),
                    Context.getSplit(v) match {
                      case Some(split) => LinCheck.Success(CapturingFun.lift(split))
                      case None        => LinCheck.Failure(errors.overusedVars(Var.Set(v)))
                    },
                    Par(SingleVar[a](), SingleVar[a]()),
                  )
                case (vars, op: Op.Prj1[a1, a2]) =>
                  Image(
                    SingleVar[a1 |*| a2](),
                    Context.getDiscard(op.unusedVar) match {
                      case Some(discard) => LinCheck.Success(CapturingFun.noCapture(shuffled.swap > shuffled.lift(discard[a1](()))))
                      case None          => LinCheck.Failure(errors.underusedVars(Var.Set(op.unusedVar)))
                    },
                    SingleVar[a1](),
                  )
                case (vars, op: Op.Prj2[a1, a2]) =>
                  Image(
                    SingleVar[a1 |*| a2](),
                    Context.getDiscard(op.unusedVar) match {
                      case Some(discard) => LinCheck.Success(CapturingFun.lift(discard[a2](())))
                      case None          => LinCheck.Failure(errors.underusedVars(Var.Set(op.unusedVar)))
                    },
                    SingleVar[a2](),
                  )
              }
          },
        ) match {
          case Exists.Some((t2, u2)) =>
            (u uniqueOutType u2) match {
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

        override def gcdSimple[X, C](that: Op.Affine[Var[X], C])(using Var[A] =:= Var[X]): Option[Tail[Var[A], Var[B] |*| C]] =
          that match
            case Map(_, v) =>
              ((v testEqual resultVar)) match
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

      case class Prj1[A1, A2](resultVar: Var[A1], unusedVar: Var[A2]) extends Affine[Var[A1 |*| A2], Var[A1]] {
        override def terminalVars(a: Varz[Var[A1 |*| A2]]): Varz[Var[A1]] =
          Varz.atom(resultVar)

        override def gcdSimple[X, C](that: Op.Affine[Var[X], C])(using ev: Var[A1 |*| A2] =:= Var[X]): Option[Tail[Var[A1 |*| A2], Var[A1] |*| C]] =
          that.prj1_gcd_this(this)(using ev.flip)

        override def prj1_gcd_this[a1, a2](that: Prj1[a1, a2])(using ev: Var[A1 |*| A2] =:= Var[a1 |*| a2]): Option[Tail[Var[a1 |*| a2], Var[a1] |*| Var[A1]]] =
          (that.resultVar testEqual this.resultVar, that.unusedVar testEqual this.unusedVar) match
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
          (that.unusedVar testEqual this.resultVar, that.resultVar testEqual this.unusedVar) match
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
              (that.resultVar1 testEqual this.resultVar, that.resultVar2 testEqual this.unusedVar) match
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

        override def gcdSimple[X, C](that: Op.Affine[Var[X], C])(using ev: Var[A1 |*| A2] =:= Var[X]): Option[Tail[Var[A1 |*| A2], Var[A2] |*| C]] =
          that.prj2_gcd_this(this)(using ev.flip)

        override def prj1_gcd_this[a1, a2](that: Prj1[a1, a2])(using ev: Var[A1 |*| A2] =:= Var[a1 |*| a2]): Option[Tail[Var[a1 |*| a2], Var[a1] |*| Var[A2]]] =
          (that.resultVar testEqual this.unusedVar, that.unusedVar testEqual this.resultVar) match
            case (Some(TypeEq(Refl())), Some(TypeEq(Refl()))) =>
              Some(shOp.lift(Unzip(that.resultVar, this.resultVar)))
            case (None, None) =>
              None
            case (Some(_), None) =>
              bug(s"Variable ${that.resultVar} appeared as a result of two different projections")
            case (None, Some(_)) =>
              bug(s"Variable ${that.unusedVar} appeared as a result of two different projections")

        override def prj2_gcd_this[a1, a2](that: Prj2[a1, a2])(using ev: Var[A1 |*| A2] =:= Var[a1 |*| a2]): Option[Tail[Var[a1 |*| a2], Var[a2] |*| Var[A2]]] =
          (that.unusedVar testEqual this.unusedVar, that.resultVar testEqual this.resultVar) match
            case (Some(TypeEq(Refl())), Some(TypeEq(Refl()))) =>
              Some(shOp.lift(this) > shOp.lift(DupVar()))
            case (None, None) =>
              None
            case (Some(_), None) =>
              bug(s"Variable ${that.unusedVar} appeared as a result of two different projections")
            case (None, Some(_)) =>
              bug(s"Variable ${that.resultVar} appeared as a result of two different projections")

        override def unzip_gcd_this[T1, T2](that: Unzip[T1, T2])(using ev: Var[A1 |*| A2] =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], (Var[T1] |*| Var[T2]) |*| Var[A2]]] =
          (that.resultVar1 testEqual this.unusedVar, that.resultVar2 testEqual this.resultVar) match
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

        override def gcdSimple[X, C](that: Op.Affine[Var[X], C])(using ev: Var[A1 |*| A2] =:= Var[X]): Option[Tail[Var[A1 |*| A2], Var[A1] |*| Var[A2] |*| C]] =
          that.unzip_gcd_this(this)(using ev.flip)

        override def prj1_gcd_this[a1, a2](that: Prj1[a1, a2])(using
          ev: Var[A1 |*| A2] =:= Var[a1 |*| a2],
        ): Option[Tail[Var[a1 |*| a2], Var[a1] |*| (Var[A1] |*| Var[A2])]] =
          (that.resultVar testEqual this.resultVar1, that.unusedVar testEqual this.resultVar2) match
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
          (that.unusedVar testEqual this.resultVar1, that.resultVar testEqual this.resultVar2) match
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
          (that.resultVar1 testEqual this.resultVar1, that.resultVar2 testEqual this.resultVar2) match
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
      }

      case class CaptureFst[A, X](x: Expr[X], resultVar: Var[X |*| A]) extends Op.Linear[Var[A], Var[X |*| A]] {
        override def terminalVars(a: Varz[Var[A]]): Varz[Var[X |*| A]] =
          Varz.atom(resultVar)

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
            (that.resultVar testEqual this.resultVar) map {
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
            (that.resultVar testEqual this.resultVar) map {
              case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                shOp.lift(this) > shOp.lift(DupVar())
            }
          }

        override def asZip[P1, P2](using ev: Var[A] =:= (P1 |*| P2)): Exists[[V1] =>> Exists[[V2] =>> (Zip[V1, V2], P1 =:= Var[V1], P2 =:= Var[V2], Var[A |*| X] =:= Var[V1 |*| V2])]] =
          varIsNotPair(ev)
      }

      case class CaptureReplace[A, Z](
        discard: (A |*| Z) -⚬ Z,
        replacement: Expr[Z],
      ) extends Op.Linear[Var[A], Var[Z]] {
        override def terminalVars(a: Varz[Var[A]]): Varz[Var[Z]] =
          Varz.atom(replacement.resultVar)

        override def gcdSimple[X, C](that: Op.Affine[Var[X], C])(using ev: Var[A] =:= Var[X]): Option[Tail[Var[A], Var[Z] |*| C]] =
          that.maskInput.visit[Option[Tail[Var[A], Var[Z] |*| C]]]([T] => (that: Op[T, C], ev: T =:= Var[X]) => {
            that match
              case cr: CaptureReplace[a, c] =>
                summon[C =:= Var[c]]
                (cr.replacement.resultVar testEqual replacement.resultVar) map {
                  case TypeEq(Refl()) =>
                    shOp.lift(CaptureReplace.this) > shOp.lift(DupVar[Z]().to[Var[Z] |*| Var[c]])
                }
              case _ =>
                None
          })

        override def prj1_gcd_this[T1, T2](that: Prj1[T1, T2])(using ev: Var[A] =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], Var[T1] |*| Var[Z]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.prj1_gcd_this")

        override def prj2_gcd_this[T1, T2](that: Prj2[T1, T2])(using ev: Var[A] =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], Var[T2] |*| Var[Z]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.prj2_gcd_this")

        override def unzip_gcd_this[T1, T2](that: Unzip[T1, T2])(using ev: Var[A] =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], (Var[T1] |*| Var[T2]) |*| Var[Z]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.unzip_gcd_this")

        override def cap1_gcd_this[T, X](that: CaptureFst[T, X])(using Var[A] =:= Var[T]): Option[Tail[Var[T], Var[X |*| T] |*| Var[Z]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.cap1_gcd_this")

        override def cap2_gcd_this[T, Y](that: CaptureSnd[T, Y])(using Var[A] =:= Var[T]): Option[Tail[Var[T], Var[T |*| Y] |*| Var[Z]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.cap2_gcd_this")

        override def asZip[P1, P2](using ev: Var[A] =:= (P1 |*| P2)): Exists[[V1] =>> Exists[[V2] =>> (Zip[V1, V2], P1 =:= Var[V1], P2 =:= Var[V2], Var[Z] =:= Var[V1 |*| V2])]] =
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
            case op: Zip[t, u]            => InputVarFocus[[x] =>> x |*| Var[u], t, Var[t |*| u]](op, Focus.fst) // arbitrarily picking the first input
            case op: Unzip[t, u]          => InputVarFocus[[x] =>> x, t |*| u, Var[t] |*| Var[u]](op, Focus.id)
            case op: Prj1[t, u]           => InputVarFocus[[x] =>> x, t |*| u, Var[t]](op, Focus.id)
            case op: Prj2[t, u]           => InputVarFocus[[x] =>> x, t |*| u, Var[u]](op, Focus.id)
            case op: Map[t, u]            => InputVarFocus[[x] =>> x, t, Var[u]](op, Focus.id)
            case op: CaptureFst[t, u]     => InputVarFocus[[x] =>> x, t, Var[u |*| t]](op, Focus.id)
            case op: CaptureSnd[t, u]     => InputVarFocus[[x] =>> x, t, Var[t |*| u]](op, Focus.id)
            case op: CaptureReplace[t, u] => InputVarFocus[[x] =>> x, t, Var[u]](op, Focus.id)
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
        (z1.resultVar testEqual z2.resultVar) map {
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

    type Tail[A, B] =
      shOp.Shuffled[A, B]

    type VTail[A, B] =
      shVOp.Shuffled[A, B]

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

    def captureReplace[A, X](discard: [B] => Unit => (A |*| B) -⚬ B, replacement: Expr[X]): Tail[Var[A], Var[X]] =
      shOp.lift(Op.CaptureReplace(discard[X](()), replacement))

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
        case Op.Zip(_)               => None
        case Op.CaptureFst(_, _)     => None
        case Op.CaptureSnd(_, _)     => None
        case Op.Unzip(_, _)          => None
        case Op.Map(_, _)            => None
        case Op.Prj1(_, _)           => None
        case Op.Prj2(_, _)           => None
        case Op.CaptureReplace(_, _) => None
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

    enum LinearRes[A, B] {
      case Exact(f: AbstractFun[A, B])
      case Closure[X, A, B](captured: Tupled[Expr, X], f: AbstractFun[X |*| A, B]) extends LinearRes[A, B]
      case Violation(e: LE)
    }

    sealed trait Unvar[A, B] {
      def uniqueOutType[C](that: Unvar[A, C]): B =:= C

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
    }
  }

  private given varIsNotPair: ([V, A, B] => (Var[V] =:= (A |*| B)) => Nothing) =
    [V, A, B] => (ev: Var[V] =:= (A |*| B)) => throw new AssertionError("Var[A] =:= (A |*| B)")

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
}