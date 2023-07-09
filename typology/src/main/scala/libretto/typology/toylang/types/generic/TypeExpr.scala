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
sealed abstract class TypeExpr[V, ->>[_, _], K, L](using
  val inKind: Kind[K],
  val outKind: OutputKind[L],
) {
  import TypeExpr._

  def from[J](using ev: J =:= K): TypeExpr[V, ->>, J, L] =
    ev.substituteContra[TypeExpr[V, ->>, *, L]](this)

  def to[M](using ev: L =:= M): TypeExpr[V, ->>, K, M] =
    ev.substituteCo[TypeExpr[V, ->>, K, *]](this)

  def vmap[W](f: V => W): TypeExpr[W, ->>, K, L] =
    this match {
      case AbstractType(v) => AbstractType(f(v))

      case UnitType() => UnitType()
      case IntType() => IntType()
      case StringType() => StringType()
      case Pair() => Pair()
      case Sum() => Sum()
      case RecCall() => RecCall()
      case Fix(f, g) => Fix(f, g)
      case x @ PFix(f, g) => import x.given; PFix(f, g)
      case ScalaTypeParams(values) => ScalaTypeParams(values)
      case BiApp(op, arg1, arg2) => BiApp(op.vcast[W], arg1, arg2)
      case AppFst(op, arg1) => AppFst(op.vcast[W], arg1)
      case AppSnd(op, arg2) => AppSnd(op.vcast[W], arg2)
      case x @ ComposeSnd(op, arg2) => import x.given; ComposeSnd(op.vcast[W], arg2)
      case x @ AppCompose(op, arg1, arg2) => import x.given; AppCompose(op.vcast[W], arg1, arg2)
      case TypeMismatch(a, b) => TypeMismatch(a, b)
    }

  def translate[-->>[_, _]](f: [k, l] => (k ->> l) => (k -->> l)): TypeExpr[V, -->>, K, L] =
    translateM[-->>, [x] =>> x](f)

  def translateM[-->>[_, _], M[_]: Monad](f: [k, l] => (k ->> l) => M[k -->> l]): M[TypeExpr[V, -->>, K, L]] = {
    this match {
      case UnitType() => UnitType().pure[M]
      case IntType() => IntType().pure[M]
      case StringType() => StringType().pure[M]
      case Pair() => Pair().pure[M]
      case Sum() => Sum().pure[M]
      case AbstractType(label) => AbstractType(label).pure[M]
      case ScalaTypeParams(ps) => ScalaTypeParams(ps).pure[M]

      case AppFst(op, a) =>
        for {
          a  <- f(a)
        } yield AppFst(op.cast[-->>], a)

      case ac @ AppCompose(op, a, g) =>
        import ac.properInKind
        for {
          a <- f(a)
          g <- f(g)
        } yield AppCompose(op.cast[-->>], a, g)

      case BiApp(op, a, b) =>
        for {
          a  <- f(a)
          b  <- f(b)
        } yield BiApp(op.cast[-->>], a, b)

      case Fix(pre, expr) =>
        for {
          expr <- f(expr)
        } yield Fix(pre, expr)

      case pf @ PFix(pre, expr) =>
        import pf.properInKind
        for {
          expr <- f(expr)
        } yield PFix(pre, expr)

      case other =>
        throw new NotImplementedError(s"$other (${summon[SourcePos]})")
    }
  }

  def transApply[F[_, _], J](
    a: ArgIntro[F[○, *], J, K],
    trans: [k, l] => (k ->> l) => F[k, l],
    transApp: [j, k, l] => (k ->> l, ArgIntro[F[○, *], j, k]) => F[j, l],
  ): TypeExpr[V, F, J, L] =
    transApplyM[F, J, [x] =>> x](a, trans, transApp)

  def transApplyM[F[_, _], J, M[_]: Monad](
    a: ArgIntro[F[○, *], J, K],
    trans: [k, l] => (k ->> l) => F[k, l],
    transApp: [j, k, l] => (k ->> l, ArgIntro[F[○, *], j, k]) => M[F[j, l]],
  ): M[TypeExpr[V, F, J, L]] =
    a.inKind.properKind match {
      case Left(j_eq_○) =>
        j_eq_○.substituteContra[[j] =>> M[TypeExpr[V, F, j, L]]](
          transApply0M(
            j_eq_○.substituteCo[ArgIntro[F[○, *], *, K]](a),
            trans,
            transApp,
          )
        )
      case Right(j) =>
        transApply1M(a, trans, transApp)(using j, summon[Monad[M]])
    }

  private def transApply0M[F[_, _], M[_]: Monad](
    args: ArgIntro[F[○, *], ○, K],
    trans: [k, l] => (k ->> l) => F[k, l],
    transApp: [j, k, l] => (k ->> l, ArgIntro[F[○, *], j, k]) => M[F[j, l]],
  ): M[TypeExpr[V, F, ○, L]] = {
    this match {
      case Pair() =>
        args match {
          case ArgIntro.IntroBoth(a1, a2) =>
            BiApp(Pair[V, F](), ArgIntro.unwrap(a1), ArgIntro.unwrap(a2)).pure[M]
          case other =>
            throw new NotImplementedError(s"$other (${summon[SourcePos]})")
        }

      case AppFst(op, arg1) =>
        import op.in2Kind
        val arg2 = ArgIntro.unwrap(args)
        Monad[M].pure(BiApp(op.cast, trans(arg1), arg2))

      case AppCompose(op, a, g) =>
        transApp(g, args).map(BiApp(op.cast, trans(a), _))

      case PFix(pre, expr) =>
        val a: ArgIntro[F[○, *], ●, K × ●] = ArgIntro.introFst(args)
        pre.applyTo(a) match {
          case Routing.ApplyRes(r, a1) =>
            transApp(expr, a1).map(Fix(r, _))
        }

      case other =>
        throw new NotImplementedError(s"Applying $other to $args (${summon[SourcePos]})")
    }
  }

  private def transApply1M[F[_, _], J: ProperKind, M[_]: Monad](
    args: ArgIntro[F[○, *], J, K],
    trans: [k, l] => (k ->> l) => F[k, l],
    transApp: [j, k, l] => (k ->> l, ArgIntro[F[○, *], j, k]) => M[F[j, l]],
  ): M[TypeExpr[V, F, J, L]] = {
    this match {
      case ComposeSnd(op, g) =>
        args match {
          case ArgIntro.IntroFst(a, f) =>
            import op.in1Kind
            transApp(g, f)
              .map(AppCompose(op.cast, ArgIntro.unwrap(a), _))
          case other =>
            throw new NotImplementedError(s"$other (${summon[SourcePos]})")
        }

      case AppCompose(op, a, g) =>
        transApp(g, args).map(AppCompose(op.cast, trans(a), _))

      case Pair() =>
        args match {
          case ArgIntro.Id() =>
            Pair().pure[M]
          case ArgIntro.IntroFst(a, f) =>
            pair1(ArgIntro.unwrap(a))
              .from(using ArgIntro.deriveId(f))
              .pure[M]
          case ArgIntro.IntroSnd(f, a) =>
            pair2(ArgIntro.unwrap(a))
              .from(using ArgIntro.deriveId(f))
              .pure[M]
          case other =>
            throw new NotImplementedError(s"$other (${summon[SourcePos]})")
        }

      case other =>
        throw new NotImplementedError(s"Applying $other to $args (${summon[SourcePos]})")
    }
  }

  def transCompose[A[_, _], J](
    a: ArgTrans[A, J, K],
    trans: [k, l] => (k ->> l) => A[k, l],
    transComp: [j, k, l] => (k ->> l, ArgTrans[A, j, k]) => A[j, l],
  ): TypeExpr[V, A, J, L] =
    transComposeM[A, J, [x] =>> x](a, trans, transComp)

  def transComposeM[A[_, _], J, M[_]: Monad](
    a: ArgTrans[A, J, K],
    trans: [k, l] => (k ->> l) => A[k, l],
    transComp: [j, k, l] => (k ->> l, ArgTrans[A, j, k]) => M[A[j, l]],
  ): M[TypeExpr[V, A, J, L]] =
    a.inKind.properKind match {
      case Left(j_eq_○) =>
        j_eq_○.substituteContra[[j] =>> M[TypeExpr[V, A, j, L]]](
          transCompose0M(
            j_eq_○.substituteCo[ArgTrans[A, *, K]](a),
            trans,
            transComp,
          )
        )
      case Right(j) =>
        transCompose1M(a, trans, transComp)(using j, summon[Monad[M]])
    }

  private def transCompose0M[F[_, _], M[_]: Monad](
    f: ArgTrans[F, ○, K],
    trans: [k, l] => (k ->> l) => F[k, l],
    transApp: [j, k, l] => (k ->> l, ArgTrans[F, j, k]) => M[F[j, l]],
  ): M[TypeExpr[V, F, ○, L]] =
    this match {
      case PFix(p, e) =>
        p.applyToTrans(ArgTrans.introFst(f)) match {
          case Routing.AppTransRes(q, g) =>
            transApp(e, g)
              .map(Fix(q, _))
        }

      case AppFst(op, a) =>
        f match {
          case ArgTrans.Wrap(b) =>
            BiApp(op.cast[F], trans(a), b).pure[M]
          case other =>
            throw new NotImplementedError(s"$other (${summon[SourcePos]})")
        }
      case AppSnd(op, b) =>
        f match {
          case ArgTrans.Wrap(a) =>
            BiApp(op.cast[F], a, trans(b)).pure[M]
          case other =>
            throw new NotImplementedError(s"$other (${summon[SourcePos]})")
        }
      case AppCompose(op, a, g) =>
        transApp(g, f)
          .map(BiApp(op.cast[F], trans(a), _))
      case other =>
        throw new NotImplementedError(s"$other (${summon[SourcePos]})")
    }

  private def transCompose1M[F[_, _], J: ProperKind, M[_]: Monad](
    f: ArgTrans[F, J, K],
    trans: [k, l] => (k ->> l) => F[k, l],
    transComp: [j, k, l] => (k ->> l, ArgTrans[F, j, k]) => M[F[j, l]],
  ): M[TypeExpr[V, F, J, L]] = {

    def goOp[K1, K2](
      op: BinaryOperator[V, ->>, K1, K2, L],
      f: ArgTrans[F, J, K1 × K2],
    ): M[TypeExpr[V, F, J, L]] = {
      import op.in1Kind
      import op.in2Kind

      f match {
        case snd @ ArgTrans.Snd(f2) =>
          composeSnd(op.cast[F], ArgTrans.unwrap(f2))(using snd.in2Kind).pure[M]
        case ArgTrans.IntroFst(f1) =>
          AppFst(op.cast[F], ArgTrans.unwrap(f1)).pure[M]
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
            appCompose(op.cast[F], trans(a), h).pure[M]
          case other =>
            throw new NotImplementedError(s"$other (${summon[SourcePos]})")
        }
      case AppCompose(op, a, g) =>
        transComp(g, f)
          .map(AppCompose(op.cast[F], trans(a), _))
      case ComposeSnd(op, g) =>
        import op.in1Kind
        f match {
          case ArgTrans.IntroFst(f1) =>
            appCompose(op.cast[F], ArgTrans.unwrap(f1), trans(g)).pure[M]
          case other =>
            throw new NotImplementedError(s"$other (${summon[SourcePos]})")
        }
      case other =>
        throw new NotImplementedError(s"Composing $other after $f (${summon[SourcePos]})")
    }
  }
}

object TypeExpr {

  sealed abstract class BinaryOperator[V, ->>[_, _], K1, K2, L](using
    k1: OutputKind[K1],
    k2: OutputKind[K2],
    l: OutputKind[L],
  ) extends TypeExpr[V, ->>, K1 × K2, L] {
    given in1Kind: OutputKind[K1] = k1
    given in2Kind: OutputKind[K2] = k2

    def cast[F[_, _]]: BinaryOperator[V, F, K1, K2, L] =
      this match {
        case Pair() => Pair()
        case Sum()  => Sum()
        case RecCall() => RecCall()
      }

    def vcast[W]: BinaryOperator[W, ->>, K1, K2, L] =
      this match {
        case Pair()    => Pair()
        case Sum()     => Sum()
        case RecCall() => RecCall()
      }
  }

  case class UnitType[V, ->>[_, _]]() extends TypeExpr[V, ->>, ○, ●]
  case class IntType[V, ->>[_, _]]() extends TypeExpr[V, ->>, ○, ●]
  case class StringType[V, ->>[_, _]]() extends TypeExpr[V, ->>, ○, ●]

  case class Pair[V, ->>[_, _]]() extends BinaryOperator[V, ->>, ●, ●, ●]
  case class Sum[V, ->>[_, _]]() extends BinaryOperator[V, ->>, ●, ●, ●]
  case class RecCall[V, ->>[_, _]]() extends BinaryOperator[V, ->>, ●, ●, ●]

  case class Fix[V, ->>[_, _], K](f: Routing[●, K], g: K ->> ●) extends TypeExpr[V, ->>, ○, ●]

  // TODO: Make the representation normalized (part of initial routing may possibly be factored out)
  case class PFix[V, ->>[_, _], K, X](
    f: Routing[K × ●, X],
    g: X ->> ●,
  )(using
    val properInKind: ProperKind[K],
  ) extends TypeExpr[V, ->>, K, ●]

  case class AbstractType[V, ->>[_, _]](label: V) extends TypeExpr[V, ->>, ○, ●]

  case class ScalaTypeParam(filename: String, line: Int, name: String)
  case class ScalaTypeParams[V, ->>[_, _]](values: Set[ScalaTypeParam]) extends TypeExpr[V, ->>, ○, ●] {
    require(values.nonEmpty)
  }
  object ScalaTypeParams {
    def one[V, ->>[_, _]](filename: String, line: Int, name: String): ScalaTypeParams[V, ->>] =
      ScalaTypeParams(Set(ScalaTypeParam(filename, line, name)))
  }

  case class BiApp[V, ->>[_, _], K1, K2, L](
    op: BinaryOperator[V, ->>, K1, K2, L],
    arg1: ○ ->> K1,
    arg2: ○ ->> K2,
  ) extends TypeExpr[V, ->>, ○, L](using summon, op.outKind)

  case class AppFst[V, ->>[_, _], K1, K2, L](
    op: BinaryOperator[V, ->>, K1, K2, L],
    arg1: ○ ->> K1,
  ) extends TypeExpr[V, ->>, K2, L](using op.in2Kind.kind, op.outKind)

  case class AppSnd[V, ->>[_, _], K1, K2, L](
    op: BinaryOperator[V, ->>, K1, K2, L],
    arg2: ○ ->> K2,
  ) extends TypeExpr[V, ->>, K1, L](using op.in1Kind.kind, op.outKind)

  case class ComposeSnd[V, ->>[_, _], K1, K2, L2, M](
    op: BinaryOperator[V, ->>, K1, L2, M],
    arg2: K2 ->> L2,
  )(using
    val properKind2: ProperKind[K2],
  ) extends TypeExpr[V, ->>, K1 × K2, M](using
    (Kind.fst(op.inKind) × ProperKind[K2]).kind,
    op.outKind,
  )

  case class AppCompose[V, ->>[_, _], K, L1, L2, M](
    op: BinaryOperator[V, ->>, L1, L2, M],
    arg1: ○ ->> L1,
    arg2: K ->> L2,
  )(using
    val properInKind: ProperKind[K],
  ) extends TypeExpr[V, ->>, K, M](using summon, op.outKind)

  case class TypeMismatch[V, ->>[_, _], K: Kind, L: OutputKind](
    a: K ->> L,
    b: K ->> L,
  ) extends TypeExpr[V, ->>, K, L]

  def abstractType[V, ->>[_, _]](label: V): TypeExpr[V, ->>, ○, ●] =
    AbstractType(label)

  def pair[V, ->>[_, _]](a: ○ ->> ●, b: ○ ->> ●): TypeExpr[V, ->>, ○, ●] =
    BiApp(Pair(), a, b)

  def sum[V, ->>[_, _]](a: ○ ->> ●, b: ○ ->> ●): TypeExpr[V, ->>, ○, ●] =
    BiApp(Sum(), a, b)

  def recCall[V, ->>[_, _]](a: ○ ->> ●, b: ○ ->> ●): TypeExpr[V, ->>, ○, ●] =
    BiApp(RecCall(), a, b)

  def pair1[V, ->>[_, _]](a: ○ ->> ●): TypeExpr[V, ->>, ●, ●] =
    AppFst(Pair(), a)

  def pair2[V, ->>[_, _]](b: ○ ->> ●): TypeExpr[V, ->>, ●, ●] =
    AppSnd(Pair(), b)

  def sum1[V, ->>[_, _]](a: ○ ->> ●): TypeExpr[V, ->>, ●, ●] =
    AppFst(Sum(), a)

  def sum2[V, ->>[_, _]](b: ○ ->> ●): TypeExpr[V, ->>, ●, ●] =
    AppSnd(Sum(), b)

  def appCompose[V, ->>[_, _], K, L1, L2, M](
    op: BinaryOperator[V, ->>, L1, L2, M],
    arg1: ○ ->> L1,
    arg2: K ->> L2,
  )(using
    k: ProperKind[K],
  ): TypeExpr[V, ->>, K, M] =
    AppCompose(op, arg1, arg2)

  def composeSnd[V, ->>[_, _], K1, K2: ProperKind, L2, M](
    op: BinaryOperator[V, ->>, K1, L2, M],
    arg2: K2 ->> L2,
  ): TypeExpr[V, ->>, K1 × K2, M] =
    ComposeSnd(op, arg2)

  def typeMismatch[V, ->>[_, _], K: Kind, L: OutputKind](
    a: K ->> L,
    b: K ->> L,
  ): TypeExpr[V, ->>, K, L] =
    TypeMismatch(a, b)
}
