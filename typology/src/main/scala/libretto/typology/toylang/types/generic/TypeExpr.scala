package libretto.typology.toylang.types.generic

import libretto.lambda.util.Applicative._
import libretto.lambda.util.{Monad, SourcePos}
import libretto.lambda.util.Monad.syntax._
import libretto.typology.kinds._
import libretto.typology.toylang.types.{AbstractTypeLabel, ArgIntro, ArgTrans, Routing}
import libretto.typology.toylang.types.ArgTrans.Wrap

/** Tree-like structure that builds up a type (or type constructor, depending on the output kind `L`).
 *  May take type parameters, represented by the input kind `K`.
 *  Each type (constructor) has a unique representation as [[TypeExpr]] (i.e. each [[TypeExpr]] is a normal form).
 *
 * @tparam V labeling of type variables
 */
sealed abstract class TypeExpr[V, K, L](using
  val inKind: Kind[K],
  val outKind: OutputKind[L],
) {
  import TypeExpr._

  def from[J](using ev: J =:= K): TypeExpr[V, J, L] =
    ev.substituteContra[TypeExpr[V, _, L]](this)

  def to[M](using ev: L =:= M): TypeExpr[V, K, M] =
    ev.substituteCo[TypeExpr[V, K, _]](this)

  def vmap[W](f: V => W): TypeExpr[W, K, L] =
    this match {
      case AbstractType(v) => AbstractType(f(v))

      case UnitType() => UnitType()
      case IntType() => IntType()
      case StringType() => StringType()
      case Pair() => Pair()
      case Sum() => Sum()
      case RecCall() => RecCall()
      case Fix(g, h) => Fix(g, h.vmap(f))
      case x @ PFix(g, h) => import x.given; PFix(g, h.vmap(f))
      case BiApp(op, arg1, arg2) => BiApp(op.vcast[W], arg1.vmap(f), arg2.vmap(f))
      case AppFst(op, arg1) => AppFst(op.vcast[W], arg1.vmap(f))
      case AppSnd(op, arg2) => AppSnd(op.vcast[W], arg2.vmap(f))
      case x @ ComposeSnd(op, arg2) => import x.given; ComposeSnd(op.vcast[W], arg2.vmap(f))
      case x @ AppCompose(op, arg1, arg2) => import x.given; AppCompose(op.vcast[W], arg1.vmap(f), arg2.vmap(f))
      case TypeMismatch(a, b) => TypeMismatch(a.vmap(f), b.vmap(f))
      case ForbiddenSelfReference(v) => ForbiddenSelfReference(f(v))
    }

  def apply[J](
    a: ArgIntro[TypeExpr[V, ○, _], J, K],
  ): TypeExpr[V, J, L] =
    a.inKind.properKind match {
      case Left(j_eq_○) =>
        j_eq_○.substituteContra[[j] =>> TypeExpr[V, j, L]](
          apply0(
            j_eq_○.substituteCo[ArgIntro[TypeExpr[V, ○, _], _, K]](a),
          )
        )
      case Right(j) =>
        apply1(a)(using j)
    }

  private def apply0(
    args: ArgIntro[TypeExpr[V, ○, _], ○, K],
  ): TypeExpr[V, ○, L] = {
    this match {
      case Pair() =>
        args match {
          case ArgIntro.IntroBoth(a1, a2) =>
            BiApp(Pair[V](), ArgIntro.unwrap(a1), ArgIntro.unwrap(a2))
          case other =>
            throw new NotImplementedError(s"$other (${summon[SourcePos]})")
        }

      case AppFst(op, arg1) =>
        import op.in2Kind
        val arg2 = ArgIntro.unwrap(args)
        BiApp(op, arg1, arg2)

      case AppCompose(op, a, g) =>
        BiApp(op, a, g.apply(args))

      case PFix(pre, expr) =>
        val a: ArgIntro[TypeExpr[V, ○, _], ●, K × ●] = ArgIntro.introFst(args)
        pre.applyTo(a) match {
          case Routing.ApplyRes(r, a1) =>
            Fix(r, expr.apply(a1))
        }

      case other =>
        throw new NotImplementedError(s"Applying $other to $args (${summon[SourcePos]})")
    }
  }

  private def apply1[J: ProperKind](
    args: ArgIntro[TypeExpr[V, ○, _], J, K],
  ): TypeExpr[V, J, L] = {
    this match {
      case ComposeSnd(op, g) =>
        args match {
          case ArgIntro.IntroFst(a, f) =>
            import op.in1Kind
            AppCompose(op, ArgIntro.unwrap(a), g.apply(f))
          case other =>
            throw new NotImplementedError(s"$other (${summon[SourcePos]})")
        }

      case AppCompose(op, a, g) =>
        AppCompose(op, a, g.apply(args))

      case Pair() =>
        args match {
          case ArgIntro.Id() =>
            Pair()
          case ArgIntro.IntroFst(a, f) =>
            pair1(ArgIntro.unwrap(a))
              .from(using ArgIntro.deriveId(f))
          case ArgIntro.IntroSnd(f, a) =>
            pair2(ArgIntro.unwrap(a))
              .from(using ArgIntro.deriveId(f))
          case other =>
            throw new NotImplementedError(s"$other (${summon[SourcePos]})")
        }

      case other =>
        throw new NotImplementedError(s"Applying $other to $args (${summon[SourcePos]})")
    }
  }

  def transCompose[J](
    a: ArgTrans[TypeExpr[V, _, _], J, K],
  ): TypeExpr[V, J, L] =
    a.inKind.properKind match {
      case Left(j_eq_○) =>
        j_eq_○.substituteContra[[j] =>> TypeExpr[V, j, L]](
          transCompose0(
            j_eq_○.substituteCo[ArgTrans[TypeExpr[V, _, _], _, K]](a),
          )
        )
      case Right(j) =>
        transCompose1(a)(using j)
    }

  private def transCompose0(
    f: ArgTrans[TypeExpr[V, _, _], ○, K],
  ): TypeExpr[V, ○, L] =
    this match {
      case PFix(p, e) =>
        p.applyToTrans(ArgTrans.introFst(f)) match {
          case Routing.AppTransRes(q, g) =>
            Fix(q, e.transCompose(g))
        }

      case AppFst(op, a) =>
        f match {
          case ArgTrans.Wrap(b) =>
            BiApp(op, a, b)
          case other =>
            throw new NotImplementedError(s"$other (${summon[SourcePos]})")
        }
      case AppSnd(op, b) =>
        f match {
          case ArgTrans.Wrap(a) =>
            BiApp(op, a, b)
          case other =>
            throw new NotImplementedError(s"$other (${summon[SourcePos]})")
        }
      case AppCompose(op, a, g) =>
        BiApp(op, a, g.transCompose(f))
      case other =>
        throw new NotImplementedError(s"$other (${summon[SourcePos]})")
    }

  private def transCompose1[J: ProperKind](
    f: ArgTrans[TypeExpr[V, _, _], J, K],
  ): TypeExpr[V, J, L] = {

    def goOp[K1, K2](
      op: BinaryOperator[V, K1, K2, L],
      f: ArgTrans[TypeExpr[V, _, _], J, K1 × K2],
    ): TypeExpr[V, J, L] = {
      import op.in1Kind
      import op.in2Kind

      f match {
        case snd @ ArgTrans.Snd(f2) =>
          composeSnd(op, ArgTrans.unwrap(f2))(using snd.in2Kind)
        case ArgTrans.IntroFst(f1) =>
          AppFst(op, ArgTrans.unwrap(f1))
        case other =>
          throw new NotImplementedError(s"$other (${summon[SourcePos]})")
      }
    }

    this match {
      case Pair() =>
        goOp(Pair(), f)
      case Sum() =>
        goOp(Sum(), f)
      case AppFst(op, a) =>
        f match {
          case ArgTrans.Wrap(h) =>
            appCompose(op, a, h)
          case other =>
            throw new NotImplementedError(s"$other (${summon[SourcePos]})")
        }
      case AppCompose(op, a, g) =>
        AppCompose(op, a, g.transCompose(f))
      case ComposeSnd(op, g) =>
        import op.in1Kind
        f match {
          case ArgTrans.IntroFst(f1) =>
            appCompose(op, ArgTrans.unwrap(f1), g)
          case other =>
            throw new NotImplementedError(s"$other (${summon[SourcePos]})")
        }
      case other =>
        throw new NotImplementedError(s"Composing $other after $f (${summon[SourcePos]})")
    }
  }
}

object TypeExpr {

  sealed abstract class BinaryOperator[V, K1, K2, L](using
    k1: OutputKind[K1],
    k2: OutputKind[K2],
    l: OutputKind[L],
  ) extends TypeExpr[V, K1 × K2, L] {
    given in1Kind: OutputKind[K1] = k1
    given in2Kind: OutputKind[K2] = k2

    def vcast[W]: BinaryOperator[W, K1, K2, L] =
      this match {
        case Pair()    => Pair()
        case Sum()     => Sum()
        case RecCall() => RecCall()
      }
  }

  case class UnitType[V]() extends TypeExpr[V, ○, ●]
  case class IntType[V]() extends TypeExpr[V, ○, ●]
  case class StringType[V]() extends TypeExpr[V, ○, ●]

  case class Pair[V]() extends BinaryOperator[V, ●, ●, ●]
  case class Sum[V]() extends BinaryOperator[V, ●, ●, ●]
  case class RecCall[V]() extends BinaryOperator[V, ●, ●, ●]

  case class Fix[V, K](
    f: Routing[●, K],
    g: TypeExpr[V, K, ●],
  ) extends TypeExpr[V, ○, ●]

  // TODO: Make the representation normalized (part of initial routing may possibly be factored out)
  // case class PFix[V, K, X](
  //   f: Routing[K × ●, X],
  //   g: X ->> ●,
  // )(using
  //   val properInKind: ProperKind[K],
  // ) extends TypeExpr[V, K, ●]
  case class PFix[V, X](
    f: Routing[● × ●, X],
    g: TypeExpr[V, X, ●],
  ) extends TypeExpr[V, ●, ●]

  case class AbstractType[V](label: V) extends TypeExpr[V, ○, ●]

  case class BiApp[V, K1, K2, L](
    op: BinaryOperator[V, K1, K2, L],
    arg1: TypeExpr[V, ○, K1],
    arg2: TypeExpr[V, ○, K2],
  ) extends TypeExpr[V, ○, L](using summon, op.outKind)

  case class AppFst[V, K1, K2, L](
    op: BinaryOperator[V, K1, K2, L],
    arg1: TypeExpr[V, ○, K1],
  ) extends TypeExpr[V, K2, L](using op.in2Kind.kind, op.outKind)

  case class AppSnd[V, K1, K2, L](
    op: BinaryOperator[V, K1, K2, L],
    arg2: TypeExpr[V, ○, K2],
  ) extends TypeExpr[V, K1, L](using op.in1Kind.kind, op.outKind)

  case class ComposeSnd[V, K1, K2, L2, M](
    op: BinaryOperator[V, K1, L2, M],
    arg2: TypeExpr[V, K2, L2],
  )(using
    val properKind2: ProperKind[K2],
  ) extends TypeExpr[V, K1 × K2, M](using
    (Kind.fst(op.inKind) × ProperKind[K2]).kind,
    op.outKind,
  )

  case class AppCompose[V, K, L1, L2, M](
    op: BinaryOperator[V, L1, L2, M],
    arg1: TypeExpr[V, ○, L1],
    arg2: TypeExpr[V, K, L2],
  )(using
    val properInKind: ProperKind[K],
  ) extends TypeExpr[V, K, M](using summon, op.outKind)

  case class TypeMismatch[V, K: Kind, L: OutputKind](
    a: TypeExpr[V, K, L],
    b: TypeExpr[V, K, L],
  ) extends TypeExpr[V, K, L]

  case class ForbiddenSelfReference[V, K: Kind, L: OutputKind](
    v: V,
  ) extends TypeExpr[V, K, L]

  def abstractType[V](label: V): TypeExpr[V, ○, ●] =
    AbstractType(label)

  def pair[V](a: TypeExpr[V, ○, ●], b: TypeExpr[V, ○, ●]): TypeExpr[V, ○, ●] =
    BiApp(Pair(), a, b)

  def sum[V](a: TypeExpr[V, ○, ●], b: TypeExpr[V, ○, ●]): TypeExpr[V, ○, ●] =
    BiApp(Sum(), a, b)

  def recCall[V](a: TypeExpr[V, ○, ●], b: TypeExpr[V, ○, ●]): TypeExpr[V, ○, ●] =
    BiApp(RecCall(), a, b)

  def pair1[V](a: TypeExpr[V, ○, ●]): TypeExpr[V, ●, ●] =
    AppFst(Pair(), a)

  def pair2[V](b: TypeExpr[V, ○, ●]): TypeExpr[V, ●, ●] =
    AppSnd(Pair(), b)

  def sum1[V](a: TypeExpr[V, ○, ●]): TypeExpr[V, ●, ●] =
    AppFst(Sum(), a)

  def sum2[V](b: TypeExpr[V, ○, ●]): TypeExpr[V, ●, ●] =
    AppSnd(Sum(), b)

  def appCompose[V, K, L1, L2, M](
    op: BinaryOperator[V, L1, L2, M],
    arg1: TypeExpr[V, ○, L1],
    arg2: TypeExpr[V, K, L2],
  )(using
    k: ProperKind[K],
  ): TypeExpr[V, K, M] =
    AppCompose(op, arg1, arg2)

  def composeSnd[V, K1, K2: ProperKind, L2, M](
    op: BinaryOperator[V, K1, L2, M],
    arg2: TypeExpr[V, K2, L2],
  ): TypeExpr[V, K1 × K2, M] =
    ComposeSnd(op, arg2)

  def typeMismatch[V, K: Kind, L: OutputKind](
    a: TypeExpr[V, K, L],
    b: TypeExpr[V, K, L],
  ): TypeExpr[V, K, L] =
    TypeMismatch(a, b)

  def forbiddenSelfReference[V, K: Kind, L: OutputKind](
    v: V,
  ): TypeExpr[V, K, L] =
    ForbiddenSelfReference(v)
}
