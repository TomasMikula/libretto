package libretto.lambda

import libretto.{lambda as ll}
import libretto.lambda.Lambdas.LinearityViolation
import libretto.lambda.util.{Applicative, BiInjective, Exists, Injective, Masked, NonEmptyList, TypeEq, UniqueTypeArg, Validated}
import libretto.lambda.util.Validated.{Invalid, Valid, invalid}
import libretto.lambda.util.TypeEq.Refl
import scala.annotation.{tailrec, targetName}

class LambdasImpl[-⚬[_, _], |*|[_, _], V, C](
  universalSplit  : Option[[X]    => Unit => X -⚬ (X |*| X)],
  universalDiscard: Option[[X, Y] => Unit => (X |*| Y) -⚬ Y],
)(using
  ssc: SymmetricSemigroupalCategory[-⚬, |*|],
  inj: BiInjective[|*|],
) extends Lambdas[-⚬, |*|, V, C] {

  given shuffle: Shuffle[|*|] = Shuffle[|*|]
  given shuffled: Shuffled.With[-⚬, |*|, shuffle.type] = Shuffled[-⚬, |*|](shuffle)
  import shuffled.shuffle.{~⚬, Transfer, TransferOpt}
  import shuffled.{Shuffled as ≈⚬, assocLR, assocRL, fst, id, ix, ixi, lift, par, pure, snd, swap, xi}

  type Var[A] = libretto.lambda.Var[V, A]

  override opaque type Context = ContextImpl[-⚬, |*|, V, C, Expr]
  override object Context extends Contexts {
    private val getResultVar =
      [A] => (a: Expr[A]) => a.resultVar

    override def fresh(info: C): Context =
      new ContextImpl[-⚬, |*|, V, C, Expr](
        info,
        getResultVar,
      )

    override def nested(info: C, parent: Context): Context =
      new ContextImpl[-⚬, |*|, V, C, Expr](
        info,
        getResultVar,
        Some(parent),
      )

    override def info(using ctx: Context): C =
      ctx.info

    override def newVar[A](label: V)(using ctx: Context): Var[A] =
      ctx.newVar[A](label)

    override def registerNonLinearOps[A](a: Expr[A])(
      split: Option[A -⚬ (A |*| A)],
      discard: Option[[B] => Unit => (A |*| B) -⚬ B],
    )(using ctx: Context): Unit =
      ctx.register(a)(split, discard)

    override def registerConstant[A](v: Var[A])(
      introduce: [x] => Unit => x -⚬ (A |*| x),
    )(using ctx: Context): Unit =
      ctx.registerConstant(v)(introduce)

    override def getSplit[A](v: Var[A])(using ctx: Context): Option[A -⚬ (A |*| A)] =
      ctx.getSplit(v) orElse universalSplit.map(_[A](()))

    override def getDiscard[A](v: Var[A])(using ctx: Context): Option[[B] => Unit => (A |*| B) -⚬ B] =
      ctx.getDiscard(v) orElse universalDiscard.map(f => [B] => (_: Unit) => f[A, B](()))

    override def getConstant[A](v: Var[A])(using ctx: Context): Option[[x] => Unit => x -⚬ (A |*| x)] =
      ctx.getConstant(v)

    override def isDefiningFor[A](v: Var[A])(using ctx: Context): Boolean =
      ctx.isDefiningFor(v)
  }

  type CapturingFun[A, B] = libretto.lambda.CapturingFun[≈⚬, |*|, Tupled[Expr, _], A, B]
  object CapturingFun {
    def noCapture[A, B](f: A ≈⚬ B): CapturingFun[A, B] =
      ll.CapturingFun.NoCapture(f)

    def id[A]: CapturingFun[A, A] =
      noCapture(shuffled.id)

    def lift[A, B](f: A -⚬ B): CapturingFun[A, B] =
      noCapture(shuffled.lift(f))

    def fromShuffle[A, B](s: A ~⚬ B): CapturingFun[A, B] =
      noCapture(shuffled.pure(s))

    def captureFst[X, A](captured: Expr[X]): CapturingFun[A, X |*| A] =
      captureFst(ll.Tupled.atom(captured))

    def captureFst[X, A](captured: Tupled[Expr, X]): CapturingFun[A, X |*| A] =
      ll.CapturingFun.Closure(captured, shuffled.id)

    def captureSnd[X, A](captured: Expr[X]): CapturingFun[A, A |*| X] =
      captureSnd(ll.Tupled.atom(captured))

    def captureSnd[X, A](captured: Tupled[Expr, X]): CapturingFun[A, A |*| X] =
      ll.CapturingFun.Closure(captured, shuffled.swap)
  }

  private type Delambdified0[A, B] = Validated[LinearityViolation[V, C], CapturingFun[A, B]]

  /**
   * AST of an expression, created by user code, before translation to point-free representation,
   * containing intermediate [[Var]]s.
   * Non-linear: includes projections and multiple occurrences of the same variable.
   */
  sealed trait Expr[B] {
    import Expr.*

    def resultVar: Var[B]

    def initialVars: Var.Set[V] =
      this match {
        case Id(a)         => Var.Set(a)
        case Map(f, _, _)  => f.initialVars
        case Zip(f, g, _)  => f.initialVars merge g.initialVars
        case ZipN(f, _)    => f.foldMap0([x] => ex => ex.initialVars, _ merge _)
        case Prj1(f, _, _) => f.initialVars
        case Prj2(f, _, _) => f.initialVars
      }

    def allVars: Var.Set[V] =
      this match
        case Id(a) => Var.Set(a)
        case Map(e, f, resultVar) => e.allVars + resultVar
        case Zip(e1, e2, resultVar) => e1.allVars merge e2.allVars + resultVar
        case ZipN(exprs, resultVar) => exprs.foldMap0([x] => ex => ex.allVars, _ merge _) + resultVar
        case Prj1(a, a1, _) => a.allVars + a1
        case Prj2(a, _, a2) => a.allVars + a2

    infix def map[C](f: B -⚬ C)(resultVar: Var[C]): Expr[C] =
      Map(this, f, resultVar)

    infix def zip[D](that: Expr[D])(resultVar: Var[B |*| D]): Expr[B |*| D] =
      Zip(this, that, resultVar)

    /** Goes from the end backwards (i.e. from the result variable towards inital variables)
     * and splits this expression at the boundary where the given predicate first returns `true`.
     * Initial variables of the resulting trimmed `Expr[B]` (second part of the returned tuple)
     * are exactly the terminal variables of the returned prefix expressions (first part of the returned tuple).
     * If in some branch the predicate never returns `true`, the expression's initial variable in that branch is returned as `Left`.
     */
    def splitAt(p: [X] => Var[X] => Boolean): Exists[[x] =>> (Tupled[[t] =>> Either[Var[t], Expr[t]], x], Expr[B])] =
      cutAt[Expr]([X] => (x: Expr[X]) => if (p(x.resultVar)) Some(x) else None)

    def cutAt[G[_]](p: [X] => Expr[X] => Option[G[X]]): Exists[[x] =>> (Tupled[[t] =>> Either[Var[t], G[t]], x], Expr[B])] =
      p(this) match {
        case Some(gb) =>
          Exists((Tupled.atom(Right(gb)), Id(resultVar)))
        case None =>
          this match {
            case Id(v) =>
              Exists((Tupled.atom(Left(v)), Id(v)))
            case Map(y, f, v) =>
              y.cutAt(p) match
                case Exists.Some((x, y)) =>
                  Exists((x, Map(y, f, v)))
            case Zip(y1, y2, v) =>
              (y1.cutAt(p), y2.cutAt(p)) match
                case (Exists.Some((x1, y1)), Exists.Some((x2, y2))) =>
                  Exists((x1 zip x2), Zip(y1, y2, v))
            case ZipN(exprs, v) =>
              Expr.cutManyAt(exprs, p) match
                case Exists.Some((a, b)) =>
                  Exists((a, ZipN(b, v)))
            case Prj1(y, v1, v2) =>
              y.cutAt(p) match
                case Exists.Some((x, y)) =>
                  Exists.Some((x, Prj1(y, v1, v2)))
            case Prj2(y, v1, v2) =>
              y.cutAt(p) match
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

    case class ZipN[A](
      exprs: Tupled[Expr, A],
      resultVar: Var[A],
    ) extends Expr[A]

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

    override def map[B, C](f: Expr[B], g: B -⚬ C)(resultVar: V)(using Context): Expr[C] =
      (f map g)(Context.newVar(resultVar))

    override def zipN[A](a: Tupled[Expr, A])(resultVar: V)(using Context): Expr[A] =
      ZipN(a, Context.newVar(resultVar))

    override def zip[B1, B2](f1: Expr[B1], f2: Expr[B2])(resultVar: V)(using Context): Expr[B1 |*| B2] =
      zipN(Tupled.atom(f1) zip Tupled.atom(f2))(resultVar)

    override def unzip[B1, B2](f: Expr[B1 |*| B2])(resultVar1: V, resultVar2: V)(using Context): (Expr[B1], Expr[B2]) = {
      val v1 = Context.newVar[B1](resultVar1)
      val v2 = Context.newVar[B2](resultVar2)
      (Prj1(f, v1, v2), Prj2(f, v1, v2))
    }

    def cutManyAt[B, G[_]](
      exprs: Tupled[Expr, B],
      p: [X] => Expr[X] => Option[G[X]],
    ): Exists[[x] =>> (Tupled[[t] =>> Either[Var[t], G[t]], x], Tupled[Expr, B])] =
      import Tupled.fromBin

      exprs.asBin match
        case Bin.Leaf(b) =>
          b.cutAt(p) match
            case Exists.Some((a, b)) =>
              Exists((a, Tupled.atom(b)))
        case Bin.Branch(b1, b2) =>
          (cutManyAt(fromBin(b1), p), cutManyAt(fromBin(b2), p)) match
            case (Exists.Some((a1, b1)), Exists.Some((a2, b2))) =>
              Exists((a1 zip a2, b1 zip b2))

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
      cutAt[B, Expr](b)([X] => (x: Expr[X]) => if (p(x.resultVar)) Some(x) else None)

    def cutAt[B, G[_]](b: Tupled[Expr, B])(p: [X] => Expr[X] => Option[G[X]]): Exists[[x] =>> (Tupled[[t] =>> Either[Var[t], G[t]], x], Tupled[Expr, B])] =
      b.asBin match {
        case Bin.Leaf(b) =>
          b.cutAt(p) match
            case Exists.Some((x, b)) =>
              Exists((x, Tupled.atom(b)))
        case Bin.Branch(l, r) =>
          ( cutAt(Tupled.fromBin(l))(p)
          , cutAt(Tupled.fromBin(r))(p)
          ) match
            case (Exists.Some((x, b1)), Exists.Some((y, b2))) =>
              Exists((x zip y, b1 zip b2))
      }
  }

  /** Multiple expression trees. */
  private type Forest[A] = Bin[|*|, Var, Expr, A]

  private object Forest {
    def unvar[VA, A](f: Forest[VA], u: Unvar[VA, A]): Tupled[Expr, A] =
      Tupled.fromBin(
        f.relabelLeafs[[x] =>> x, Unvar, A](
          u,
          [X, IX] => (u: Unvar[Var[X], IX]) => u.uniqueOutType[X](Unvar.SingleVar[X]()),
        )
      )

    def upvar[A](exprs: Tupled[Expr, A]): Exists[[VA] =>> (Forest[VA], Unvar[VA, A])] =
      exprs.asBin.relabelLeafs[Var, [a, va] =>> Unvar[va, a]](
        [X] => (_: Unit) => Unvar.SingleVar(),
        [A1, A2, VA1, VA2] => (u1: Unvar[VA1, A1], u2: Unvar[VA2, A2]) => u1 zip u2,
      ) match
        case Exists.Some((u, f)) => Exists((f, u))
  }

  private type Discarder[A] =
    [B] => Unit => (A |*| B) -⚬ B

  override def eliminateLocalVariables[A, B](
    boundVar: Var[A],
    expr: Expr[B],
  )(using
    ctx: Context,
  ): Delambdified[A, B] = {
    // Before the actual elimination,
    // include unused expressions with registered discarders.`

    var usedVars: Var.Set[V] =
      expr.allVars
    var toElim: Var.Map[V, [A] =>> (Expr[A], Discarder[A])] =
      Var.Map.empty

    ctx.registeredDiscarders.foreach { case Exists.Some((exp, discarder)) =>
      if (!usedVars.containsVar(exp.resultVar)) {
        val expVars = exp.allVars

        // remove expressions previously thought unused, but they now become used via `exp`
        toElim = toElim -- expVars

        toElim = toElim + (exp.resultVar, (exp, discarder))
        usedVars = usedVars merge expVars
      }
    }

    attachDiscarded(expr, toElim.values) match
      case Exists.Some((exprs, discard)) =>
        eliminateLocalVariablesFromForest(boundVar, exprs)
          .map(_
            .mapFun([X, Y] => f => f.fold)
            .andThen(discard)
          )

  }

  private def attachDiscarded[B](
    expr: Expr[B],
    toElim: List[Exists[[X] =>> (Expr[X], Discarder[X])]],
  ): Exists[[A] =>> (Tupled[Expr, A], A -⚬ B)] = {

    val init: Exists[[A] =>> (Tupled[Expr, A], A -⚬ B)] =
      Exists((Tupled.atom(expr), ssc.id[B]))

    toElim.foldLeft(init) { (acc, ed) =>
      (acc, ed) match {
        case (e1 @ Exists.Some((acc, g)), e2 @ Exists.Some((exp, discarder))) =>
          val acc1: Tupled[Expr, e2.T |*| e1.T] =
            Tupled.atom(exp) zip acc
          Exists((acc1, discarder(()) > g))
      }
    }
  }

  private def eliminateLocalVariablesFromForest[A, B](
    boundVar: Var[A],
    exprs: Tupled[Expr, B],
  )(using Context): Delambdified0[A, B] = {
    import libretto.lambda.CapturingFun.{Closure, NoCapture}

    extractFunctionFromForest(boundVar, exprs) flatMap {
      case Closure(y, f) => // eliminate all constant expressions from captured expressions
        // split captured expressions at context boundary
        Expr.splitAt(y) { [t] => (v: Var[t]) =>
          !Context.isDefiningFor(v)
        } match {
          case Exists.Some((x, y)) =>
            type InnerVarOrOuterExpr[T] = Either[Var[T], Expr[T]]

            def go[X, Y](
              boundary: Bin[|*|, [t] =>> t, InnerVarOrOuterExpr, X],
              captured: Tupled[Expr, Y],
              f: (Y |*| A) ≈⚬ B,
              alreadyEliminated: Var.Set[V],
            ): (Delambdified0[A, B], Var.Set[V]) =
              boundary match {
                case Bin.Leaf(Left(v)) =>
                  if (alreadyEliminated containsVar v)
                    (Valid(Closure(captured, f)), alreadyEliminated)
                  else (
                    Context.getConstant(v) match {
                      case Some(intro) =>
                        extractFunctionFromForest(v, captured).map :
                          case NoCapture(g)  => NoCapture(lift(intro[A](())) > fst(g) > f)
                          case Closure(x, g) => Closure(x, snd(lift(intro[A](()))) > assocRL > fst(g) > f)
                      case None =>
                        bug(s"Unexpected variable that neither derives from λ nor is a constant")
                    },
                    alreadyEliminated + v
                  )
                case Bin.Leaf(Right(x)) =>
                  val v = x.resultVar
                  if (alreadyEliminated containsVar v)
                    (Valid(Closure(captured, f)), alreadyEliminated)
                  else (
                    extractFunctionFromForest(v, captured).map {
                      case NoCapture(g)  => Closure(Tupled.atom(x), fst(g) > f)
                      case Closure(y, g) => Closure(y zip Tupled.atom(x), fst(g) > f)
                    },
                    alreadyEliminated + v
                  )
                case Bin.Branch(l, r) =>
                  go(r, captured, f, alreadyEliminated) match {
                    case (Valid(Closure(x, f)), eliminatedVars) => go(l, x, f, eliminatedVars)
                    case other                                  => other
                  }
              }

            go(x.asBin, y, f, Var.Set(boundVar))._1
        }
      case f @ NoCapture(_) =>
        Valid(f)
    }
  }

  override def switch[<+>[_, _], A, B](
    cases: Sink[DelambdifiedSuccess, <+>, A, B],
    sum: [X, Y] => (X -⚬ B, Y -⚬ B) => (X <+> Y) -⚬ B,
    distribute: [X, Y, Z] => Unit => (X |*| (Y <+> Z)) -⚬ ((X |*| Y) <+> (X |*| Z))
  )(using
    Context,
  ): Validated[LinearityViolation[V, C], DelambdifiedSuccess[A, B]] =
    switchImpl(cases, sum, distribute)

  private def bug(msg: String): Nothing =
    throw new AssertionError(msg)

  private def extractFunctionFromForest[A, B](
    boundVar: Var[A],
    exprs: Tupled[Expr, B],
  )(using
    ctx: Context,
  ): Delambdified0[A, B] = {
    import libretto.lambda.CapturingFun.{Closure, NoCapture}

    Forest.upvar(exprs) match { case Exists.Some((exprs, u)) =>
      eliminateFromForest(boundVar, exprs) match {
        case EliminatedFromForest.FoundEach(arr) =>
          arr.extract(u).map :
            case NoCapture(f)  => NoCapture(f)
            case Closure(x, f) => Closure(x, f)

        case EliminatedFromForest.FoundSome(x, arr, s) =>
          s.preShuffle(u) match {
            case Exists.Some((u, s)) =>
              Unvar.objectMap.unpair(u) match
                case Unvar.objectMap.Unpaired.Impl(u1, u2) =>
                  arr.extract(u2).map :
                    case NoCapture(f)  => Closure(Forest.unvar(x, u1), snd(f) > pure(s))
                    case Closure(y, f) => Closure(Forest.unvar(x, u1) zip y, assocLR > snd(f) > pure(s))
          }
        case EliminatedFromForest.NotFound() =>
          Context.getDiscard(boundVar) match
            case Some(discardFst) => Valid(Closure(Forest.unvar(exprs, u), swap > lift(discardFst(()))))
            case None             => invalid(LinearityViolation.unusedVar(boundVar, Context.info))
      }
    }
  }

  private def eliminateFromForest[A, VB](
    boundVar: Var[A],
    exprs: Forest[VB],
  )(using
    Context,
  ): EliminatedFromForest[A, VB] = {
    import EliminatedFromForest.{FoundEach, FoundSome, NotFound}

    exprs match {
      case Bin.Leaf(b) =>
        eliminate(boundVar, b) match
          case EliminateRes.Found(arr) => FoundEach(arr)
          case EliminateRes.NotFound() => NotFound()
      case br: Bin.Branch[br, lf, f, b1, b2] =>
        val b1 = br.l
        val b2 = br.r
        ( eliminateFromForest(boundVar, b1)
        , eliminateFromForest(boundVar, b2)
        ) match {
          case (FoundEach(f1),       FoundEach(f2)      ) => FoundEach(f1 interweave f2)
          case (FoundEach(f1),       FoundSome(y, f2, t)) => FoundSome(y, f1 interweave f2, ~⚬.xi > ~⚬.snd(t))
          case (FoundEach(f1),       NotFound()         ) => FoundSome(b2, f1, ~⚬.swap)
          case (FoundSome(x, f1, s), FoundEach(f2)      ) => FoundSome(x, f1 interweave f2, ~⚬.assocRL > ~⚬.fst(s))
          case (FoundSome(x, f1, s), FoundSome(y, f2, t)) => FoundSome(x zip y, f1 interweave f2, ~⚬.ixi > ~⚬.par(s, t))
          case (FoundSome(x, f1, s), NotFound()         ) => FoundSome(x zip b2, f1, ~⚬.ix > ~⚬.fst(s))
          case (NotFound(),          FoundEach(f2)      ) => FoundSome(b1, f2, ~⚬.id)
          case (NotFound(),          FoundSome(y, f2, t)) => FoundSome(b1 zip y, f2, ~⚬.assocLR > ~⚬.snd(t))
          case (NotFound(),          NotFound()         ) => NotFound()
        }
    }
  }

  // Note: The variable is only searched for among initial variables of the expression,
  // not in any (intermediate) results.
  private def eliminate[A, B](v: Var[A], expr: Expr[B])(using Context): EliminateRes[A, B] = {
    import EliminateRes.{Found, NotFound}

    expr match
      case Expr.Id(w) =>
        (v testEqual w) match
          case Some(ev) => Found(HybridArrow.id(v).to(using ev.liftCo[Var]))
          case None     => NotFound()
      case Expr.Map(f, g, resultVar) =>
        eliminate(v, f) match
          case NotFound() => NotFound()
          case Found(arr) => Found(arr > HybridArrow.map(g, resultVar))
      case Expr.ZipN(exprs, resultVar) =>
        import EliminatedFromForest.{FoundEach, FoundSome, NotFound}
        Forest.upvar(exprs) match
          case Exists.Some((f, u)) =>
            eliminateFromForest(v, f) match
              case FoundEach(g)       => Found(g > HybridArrow.zipN(u, resultVar))
              case FoundSome(x, g, s) => Found(g > HybridArrow.captureN(x, s, u, resultVar))
              case NotFound()         => EliminateRes.NotFound()
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
    case Found[A, X, B](arr: HybridArrow[A, Var[B]]) extends EliminateRes[A, B]
    case NotFound()
  }

  private enum EliminatedFromForest[A, VB] {
    case FoundEach[A, VB](arr: HybridArrow[A, VB]) extends EliminatedFromForest[A, VB]

    case FoundSome[A, VB, VX, VC](
      captured: Forest[VX],
      arr: HybridArrow[A, VB],
      s: (VX |*| VB) ~⚬ VC,
    ) extends EliminatedFromForest[A, VC]

    case NotFound()
  }

  private case class HybridArrow[A, B](v: Var[A], tail: HybridArrow.Tail[Var[A], B]) {
    import HybridArrow.*

    def >[C](that: Tail[B, C]): HybridArrow[A, C] =
      HybridArrow(v, tail > that)

    def to[C](using ev: B =:= C): HybridArrow[A, C] =
      ev.substituteCo(this)

    infix def interweave[C](that: HybridArrow[A, C]): HybridArrow[A, B |*| C] = {
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
    ): Delambdified0[A, Y] = {
      val t1: VTail[Var[A], B] =
        tail.sweepL[Vars, VarOp](
          Vars.atom(v),
          [p, q] => (p: Vars[p], op: Op[p, q]) => {
            val q = op.terminalVars(p)
            ((p, op), q)
          }
        )._1

      type Arr[T, U] = Validated[LinearityViolation[V, C], CapturingFun[T, U]]
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
                case (vars, op: Op.ZipN[a, y]) =>
                  MappedMorphism(op.u, Valid(CapturingFun.id), SingleVar[y]())
                case (vars, op: Op.Map[a, b]) =>
                  MappedMorphism(SingleVar[a](), Valid(CapturingFun.lift(op.f)), SingleVar[b]())
                case (vars, _: Op.Unzip[a1, a2]) =>
                  MappedMorphism(SingleVar[a1 |*| a2](), Valid(CapturingFun.id), Par(SingleVar[a1](), SingleVar[a2]()))
                case (vars, op: Op.CaptureN[vx, va, vb, b]) =>
                  op.s.preShuffle(op.u) match
                    case Exists.Some((u, s)) =>
                      val u12 = Unvar.objectMap.unpair(u)
                      val x = Forest.unvar(op.x, u12.f1)
                      MappedMorphism(
                        u12.f2,
                        Valid(CapturingFun.captureFst[u12.X1, u12.X2](x) > CapturingFun.fromShuffle(s.from(using u12.ev.flip))),
                        SingleVar[b](),
                      )
                case (vars, op: Op.DupVar[a]) =>
                  val v = vars.getValue[a]
                  MappedMorphism(
                    SingleVar[a](),
                    Context.getSplit(v) match {
                      case Some(split) => Valid(CapturingFun.lift(split))
                      case None        => invalid(LinearityViolation.overusedVar(v))
                    },
                    Par(SingleVar[a](), SingleVar[a]()),
                  )
                case (vars, op: Op.Prj1[a1, a2]) =>
                  MappedMorphism(
                    SingleVar[a1 |*| a2](),
                    Context.getDiscard(op.unusedVar) match {
                      case Some(discard) => Valid(CapturingFun.noCapture(shuffled.swap > shuffled.lift(discard[a1](()))))
                      case None          => invalid(LinearityViolation.unusedVar(op.unusedVar, Context.info))
                    },
                    SingleVar[a1](),
                  )
                case (vars, op: Op.Prj2[a1, a2]) =>
                  MappedMorphism(
                    SingleVar[a1 |*| a2](),
                    Context.getDiscard(op.unusedVar) match {
                      case Some(discard) => Valid(CapturingFun.lift(discard[a2](())))
                      case None          => invalid(LinearityViolation.unusedVar(op.unusedVar, Context.info))
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

      t2
        .traverse[Validated[LinearityViolation[V, C], _], CapturingFun]([p, q] => op => op)
        .map(_.fold)
    }
  }

  private object HybridArrow {
    sealed trait Op[A, B] {
      import Op.*

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

      def terminalVars(a: Vars[A]): Vars[B]

      def maskInput: Masked[Op[*, B], A] =
        Masked[Op[*, B], A](this)

      def from[Z](using ev: Z =:= A): Op[Z, B] =
        ev.substituteContra[Op[*, B]](this)

      def to[C](using ev: B =:= C): Op[A, C] =
        ev.substituteCo(this)
    }
    object Op {
      sealed trait Affine[A, B] extends Op[A, B] {
        infix def gcdSimple[X, C](that: Op.Affine[Var[X], C])(using A =:= Var[X]): Option[Tail[A, B |*| C]]
        def prj1_gcd_this[T1, T2](that: Prj1[T1, T2])(using ev: A =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], Var[T1] |*| B]]
        def prj2_gcd_this[T1, T2](that: Prj2[T1, T2])(using ev: A =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], Var[T2] |*| B]]
        def unzip_gcd_this[T1, T2](that: Unzip[T1, T2])(using ev: A =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], (Var[T1] |*| Var[T2]) |*| B]]
        def capN_gcd_this[VX, T, VC, C](that: CaptureN[VX, Var[T], VC, C])(using A =:= Var[T]): Option[Tail[Var[T], Var[C] |*| B]]
        def zip1_gcd_this[T](that: ZipN[Var[T], T])(using A =:= Var[T]): Option[Tail[Var[T], Var[T] |*| B]]

        def asZipN[VP1, VP2](using A =:= (VP1 |*| VP2)): Exists[[B0] =>> (ZipN[A, B0], B =:= Var[B0])]

        override def from[Z](using ev: Z =:= A): Op.Affine[Z, B] = ev.substituteContra[Op.Affine[_, B]](this)
        override def to[C](using ev: B =:= C): Op.Affine[A, C]   = ev.substituteCo(this)
      }

      sealed trait Linear[A, B] extends Affine[A, B]

      case class ZipN[VA, A](u: Unvar[VA, A], resultVar: Var[A]) extends Op.Linear[VA, Var[A]] {
        override def terminalVars(a: Vars[VA]): Vars[Var[A]] =
          Vars.atom(resultVar)

        override def gcdSimple[X, C](that: Op.Affine[Var[X], C])(using ev: VA =:= Var[X]): Option[Tail[VA, Var[A] |*| C]] =
          u match
            case Unvar.SingleVar() =>
              ev match { case TypeEq(Refl()) => that.zip1_gcd_this[X](this) }
            case _: Unvar.Par[va1, va2, a1, a2] =>
              varIsNotPair[X, va1, va2](ev.flip)

        override def prj1_gcd_this[T1, T2](that: Prj1[T1, T2])(using ev: VA =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], Var[T1] |*| Var[A]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.prj1_gcd_this")

        override def prj2_gcd_this[T1, T2](that: Prj2[T1, T2])(using ev: VA =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], Var[T2] |*| Var[A]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.prj2_gcd_this")

        override def unzip_gcd_this[T1, T2](that: Unzip[T1, T2])(using ev: VA =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], (Var[T1] |*| Var[T2]) |*| Var[A]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.unzip_gcd_this")

        override def capN_gcd_this[VX, T, VC, C](that: CaptureN[VX, Var[T], VC, C])(using VA =:= Var[T]): Option[Tail[Var[T], Var[C] |*| Var[A]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.capN_gcd_this")

        override def zip1_gcd_this[T](that: ZipN[Var[T], T])(using ev: VA =:= Var[T]): Option[Tail[Var[T], Var[T] |*| Var[A]]] =
          u match
            case Unvar.SingleVar() =>
              ev match { case TypeEq(Refl()) => Some(shOp.lift(DupVar[T]())) }
            case u: Unvar.Par[va1, va2, a1, a2] =>
              varIsNotPair[T, va1, va2](ev.flip)

        override def asZipN[VP1, VP2](using VA =:= (VP1 |*| VP2)): Exists[[B0] =>> (ZipN[VA, B0], Var[A] =:= Var[B0])] =
          Exists((this, summon))
      }

      case class Map[A, B](f: A -⚬ B, resultVar: Var[B]) extends Op.Linear[Var[A], Var[B]] {
        override def terminalVars(a: Vars[Var[A]]): Vars[Var[B]] =
          Vars.atom(resultVar)

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

        override def capN_gcd_this[VX, T, VC, C](that: CaptureN[VX, Var[T], VC, C])(using Var[A] =:= Var[T]): Option[Tail[Var[T], Var[C] |*| Var[B]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.capN_gcd_this")

        override def zip1_gcd_this[T](that: ZipN[Var[T], T])(using Var[A] =:= Var[T]): Option[Tail[Var[T], Var[T] |*| Var[B]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.zip1_gcd_this")

        override def asZipN[VP1, VP2](using ev: Var[A] =:= (VP1 |*| VP2)): Exists[[B0] =>> (ZipN[Var[A], B0], Var[B] =:= Var[B0])] =
          varIsNotPair(ev)
      }

      case class Prj1[A1, A2](resultVar: Var[A1], unusedVar: Var[A2]) extends Affine[Var[A1 |*| A2], Var[A1]] {
        override def terminalVars(a: Vars[Var[A1 |*| A2]]): Vars[Var[A1]] =
          Vars.atom(resultVar)

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

        override def capN_gcd_this[VX, T, VC, C](that: CaptureN[VX, Var[T], VC, C])(using Var[A1 |*| A2] =:= Var[T]): Option[Tail[Var[T], Var[C] |*| Var[A1]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.capN_gcd_this")

        override def zip1_gcd_this[T](that: ZipN[Var[T], T])(using Var[A1 |*| A2] =:= Var[T]): Option[Tail[Var[T], Var[T] |*| Var[A1]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.zip1_gcd_this")

        override def asZipN[VP1, VP2](using ev: Var[A1 |*| A2] =:= (VP1 |*| VP2)): Exists[[B0] =>> (ZipN[Var[A1 |*| A2], B0], Var[A1] =:= Var[B0])] =
          varIsNotPair(ev)
      }

      case class Prj2[A1, A2](unusedVar: Var[A1], resultVar: Var[A2]) extends Affine[Var[A1 |*| A2], Var[A2]] {
        override def terminalVars(a: Vars[Var[A1 |*| A2]]): Vars[Var[A2]] =
          Vars.atom(resultVar)

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

        override def capN_gcd_this[VX, T, VC, C](that: CaptureN[VX, Var[T], VC, C])(using Var[A1 |*| A2] =:= Var[T]): Option[Tail[Var[T], Var[C] |*| Var[A2]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.capN_gcd_this")

        override def zip1_gcd_this[T](that: ZipN[Var[T], T])(using Var[A1 |*| A2] =:= Var[T]): Option[Tail[Var[T], Var[T] |*| Var[A2]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.zip1_gcd_this")

        override def asZipN[VP1, VP2](using ev: Var[A1 |*| A2] =:= (VP1 |*| VP2)): Exists[[B0] =>> (ZipN[Var[A1 |*| A2], B0], Var[A2] =:= Var[B0])] =
          varIsNotPair(ev)
      }

      case class Unzip[A1, A2](resultVar1: Var[A1], resultVar2: Var[A2]) extends Op.Linear[Var[A1 |*| A2], Var[A1] |*| Var[A2]] {
        override def terminalVars(a: Vars[Var[A1 |*| A2]]): Vars[Var[A1] |*| Var[A2]] =
          Vars.zip(Vars.atom(resultVar1), Vars.atom(resultVar2))

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

        override def capN_gcd_this[VX, T, VC, C](that: CaptureN[VX, Var[T], VC, C])(using Var[A1 |*| A2] =:= Var[T]): Option[Tail[Var[T], Var[C] |*| (Var[A1] |*| Var[A2])]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.capN_gcd_this")

        override def zip1_gcd_this[T](that: ZipN[Var[T], T])(using Var[A1 |*| A2] =:= Var[T]): Option[Tail[Var[T], Var[T] |*| (Var[A1] |*| Var[A2])]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.zip1_gcd_this")

        override def asZipN[VP1, VP2](using ev: Var[A1 |*| A2] =:= (VP1 |*| VP2)): Exists[[B0] =>> (ZipN[Var[A1 |*| A2], B0], (Var[A1] |*| Var[A2]) =:= Var[B0])] =
          varIsNotPair(ev)
      }

      case class DupVar[A]() extends Op[Var[A], Var[A] |*| Var[A]] {
        override def terminalVars(a: Vars[Var[A]]): Vars[Var[A] |*| Var[A]] =
          Vars.zip(a, a)
      }

      case class CaptureN[VX, VA, VB, B](
        x: Forest[VX],
        s: (VX |*| VA) ~⚬ VB,
        u: Unvar[VB, B],
        resultVar: Var[B],
      ) extends Op.Linear[VA, Var[B]] {
        override def terminalVars(a: Vars[VA]): Vars[Var[B]] =
          Vars.atom(resultVar)

        override def gcdSimple[T, C](that: Affine[Var[T], C])(using ev: VA =:= Var[T]): Option[Tail[VA, Var[B] |*| C]] =
          ev match
            case TypeEq(Refl()) =>
              that.capN_gcd_this[VX, T, VB, B](this)

        override def prj1_gcd_this[T1, T2](that: Prj1[T1, T2])(using ev: VA =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], Var[T1] |*| Var[B]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.prj1_gcd_this")

        override def prj2_gcd_this[T1, T2](that: Prj2[T1, T2])(using ev: VA =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], Var[T2] |*| Var[B]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.prj2_gcd_this")

        override def unzip_gcd_this[T1, T2](that: Unzip[T1, T2])(using ev: VA =:= Var[T1 |*| T2]): Option[Tail[Var[T1 |*| T2], Var[T1] |*| Var[T2] |*| Var[B]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.unzip_gcd_this")

        override def capN_gcd_this[VX, T, VC, C](that: CaptureN[VX, Var[T], VC, C])(using VA =:= Var[T]): Option[Tail[Var[T], Var[C] |*| Var[B]]] =
          (that.resultVar testEqual this.resultVar) map {
            case TypeEq(Refl()) =>
              shOp.lift(that) > shOp.lift(DupVar())
          }

        override def zip1_gcd_this[T](that: ZipN[Var[T], T])(using VA =:= Var[T]): Option[Tail[Var[T], Var[T] |*| Var[B]]] =
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.zip1_gcd_this")

        override def asZipN[VP1, VP2](using VA =:= (VP1 |*| VP2)): Exists[[B0] =>> (ZipN[VA, B0], Var[B] =:= Var[B0])] =
          // TODO: this will be problematic
          UnhandledCase.raise(s"${this.getClass.getSimpleName}.asZipN")
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
            case op: Unzip[t, u] => InputVarFocus[[x] =>> x, t |*| u, Var[t] |*| Var[u]](op, Focus.id)
            case op: Prj1[t, u]  => InputVarFocus[[x] =>> x, t |*| u, Var[t]](op, Focus.id)
            case op: Prj2[t, u]  => InputVarFocus[[x] =>> x, t |*| u, Var[u]](op, Focus.id)
            case op: Map[t, u]   => InputVarFocus[[x] =>> x, t, Var[u]](op, Focus.id)
            case op: CaptureN[x, a, b, c] =>
              op.s.preShuffle(op.u) match
                case Exists.Some((u, s)) =>
                  val u12 = Unvar.objectMap.unpair(u)
                  val ua = u12.f2
                  pickSomeFromUnvar(ua, Focus.id, op)
            case op: ZipN[a, b] =>
              pickSomeFromUnvar(op.u, Focus.id, op)
          }

        private def pickSomeFromUnvar[F[_], VX, X, B](
          u: Unvar[VX, X],
          f: Focus[|*|, F],
          op: Op.Affine[F[VX], B],
        ): InputVarFocus[F[VX], B] =
          u match
            case Unvar.SingleVar() =>
              summon[VX =:= Var[X]]
              InputVarFocus[F, X, B](op, f)
            case u: Unvar.Par[vx1, vx2, x1, x2] =>
              // arbitrarily picking the first part
              pickSomeFromUnvar[[x] =>> F[x |*| vx2], vx1, x1, B](u.u1, f compose Focus.fst, op)
      }

      def gcd[C[_], D[_], X, Y, Z](
        f: Op.Affine[C[Var[X]], Y],
        g: Op.Affine[D[Var[X]], Z],
      )(
        C: Focus[|*|, C],
        D: Focus[|*|, D],
      ): Option[Tail[C[Var[X]], Y |*| Z]] = {
        import shOp.shuffle.{zip as zipEq}

        (C, D) match {
          case (Focus.Id(), Focus.Id()) =>
            f gcdSimple g
          case (c: Focus.Fst[p, c1, y], d: Focus.Fst[q, d1, z]) =>
            f.asZipN[c1[Var[X]], y] match
              case Exists.Some((z1, TypeEq(Refl()))) =>
                g.asZipN[d1[Var[X]], z] match
                  case Exists.Some((z2, TypeEq(Refl()))) =>
                    gcdZipNs(z1, z2)
          case (c: Focus.Snd[p, c2, y], d: Focus.Snd[q, d2, z]) =>
            f.asZipN[y, c2[Var[X]]] match
              case Exists.Some((z1, TypeEq(Refl()))) =>
                g.asZipN[z, d2[Var[X]]] match
                  case Exists.Some((z2, TypeEq(Refl()))) =>
                    gcdZipNs(z1, z2)
          case _ =>
            None
        }
      }

      private def gcdZipNs[VA, A, VB, B](
        za: ZipN[VA, A],
        zb: ZipN[VB, B],
      ): Option[Tail[VA, Var[A] |*| Var[B]]] =
        (za.resultVar testEqual zb.resultVar) map {
          case TypeEq(Refl()) =>
            shOp.lift(za) > shOp.lift(DupVar())
        }
    }

    type Vars[A] = Bin[|*|, Var, Var, A]
    object Vars {
      def atom[A](a: Var[A]): Vars[Var[A]] =
        Bin.Leaf(a)

      def zip[A, B](a: Vars[A], b: Vars[B]): Vars[A |*| B] =
        Bin.Branch(a, b)
    }

    val shOp = Shuffled[Op, |*|](shuffled.shuffle)
    import shOp.shuffle.{zip as zipEq}

    type VarOp[A, B] = (Vars[A], Op[A, B])
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
      captureN(Bin.Leaf(x), ~⚬.id[Var[X] |*| Var[A]], Unvar.Par(Unvar.SingleVar(), Unvar.SingleVar()), resultVar)

    def captureSnd[A, X](x: Expr[X], resultVar: Var[A |*| X]): Tail[Var[A], Var[A |*| X]] =
      captureN(Bin.Leaf(x), ~⚬.swap[Var[X], Var[A]], Unvar.Par(Unvar.SingleVar(), Unvar.SingleVar()), resultVar)

    def captureN[VX, VA, VB, B](x: Forest[VX], s: (VX |*| VA) ~⚬ VB, u: Unvar[VB, B], resultVar: Var[B]): Tail[VA, Var[B]] =
      shOp.lift(Op.CaptureN(x, s, u, resultVar))

    def zip[A1, A2](resultVar: Var[A1 |*| A2]): Tail[Var[A1] |*| Var[A2], Var[A1 |*| A2]] =
      zipN(Unvar.Par(Unvar.SingleVar(), Unvar.SingleVar()), resultVar)

    def zipN[VA, A](u: Unvar[VA, A], resultVar: Var[A]): Tail[VA, Var[A]] =
      shOp.lift(Op.ZipN(u, resultVar))

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
        case ChaseBwRes.Transported(_, _) =>
          None
        case r: ChaseBwRes.OriginatesFrom[a, f, v, w, x, g] =>
          pullBump(r.pre, r.f, r.post.plug, op)(r.i, r.w, D)
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
        case Op.ZipN(_, _)           => None
        case Op.Unzip(_, _)          => None
        case Op.Map(_, _)            => None
        case Op.Prj1(_, _)           => None
        case Op.Prj2(_, _)           => None
        case Op.CaptureN(_, _, _, _) => None
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
          pushBump(r.pre.plug, r.f, r.post, op)(r.v, r.g, D)
        case shOp.ChaseFwRes.Transported(_, _) =>
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
      obstacle.maskInput.visit[Option[Tail[A, B |*| Y]]]([CX] => (o: Op[CX, W], ev: CX =:= C[Var[X]]) => {
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
  }

  sealed trait Unvar[A, B] {
    infix def uniqueOutType[C](that: Unvar[A, C]): B =:= C

    infix def zip[C, D](that: Unvar[C, D]): Unvar[A |*| C, B |*| D] =
      Unvar.Par(this, that)

    def maskInput: Masked[Unvar[_, B], A] =
      Masked(this)

    def from[Z](using ev: Z =:= A): Unvar[Z, B] =
      ev.substituteContra[Unvar[_, B]](this)
  }
  object Unvar {
    case class SingleVar[V]() extends Unvar[Var[V], V] {
      override def uniqueOutType[C](that: Unvar[Var[V], C]): V =:= C =
        that.maskInput.visit[V =:= C]([VV] => (that: Unvar[VV, C], ev: VV =:= Var[V]) => {
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
        that.maskInput.visit[(X1 |*| X2) =:= C]([A] => (that: Unvar[A, C], ev: A =:= (A1 |*| A2)) => {
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

    given objectMap: SemigroupalObjectMap[|*|, |*|, Unvar] =
      new SemigroupalObjectMap[|*|, |*|, Unvar] {
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