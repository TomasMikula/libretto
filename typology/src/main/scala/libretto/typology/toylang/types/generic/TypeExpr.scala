package libretto.typology.toylang.types.generic

import libretto.lambda.util.Applicative._
import libretto.lambda.util.Monad
import libretto.lambda.util.Monad.syntax._
import libretto.typology.kinds._
import libretto.typology.toylang.types.{AbstractTypeLabel, ArgIntro, ArgTrans, Routing}
import libretto.typology.toylang.types.ArgTrans.Wrap

/** Tree-like structure that builds up a type (or type constructor, depending on the output kind `L`).
 *  May take type parameters, represented by the input kind `K`.
 *  Each type (constructor) has a unique representation as [[TypeExpr]] (i.e. each [[TypeExpr]] is a normal form).
 */
sealed abstract class TypeExpr[->>[_, _], K, L](using
  val inKind: Kind[K],
  val outKind: OutputKind[L],
) {
  import TypeExpr._

  def from[J](using ev: J =:= K): TypeExpr[->>, J, L] =
    ev.substituteContra[TypeExpr[->>, *, L]](this)

  def to[M](using ev: L =:= M): TypeExpr[->>, K, M] =
    ev.substituteCo[TypeExpr[->>, K, *]](this)

  def translate[-->>[_, _]](f: [k, l] => (k ->> l) => (k -->> l)): TypeExpr[-->>, K, L] =
    translateM[-->>, [x] =>> x](f)

  def translateM[-->>[_, _], M[_]: Monad](f: [k, l] => (k ->> l) => M[k -->> l]): M[TypeExpr[-->>, K, L]] = {
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
        throw new NotImplementedError(s"$other")
    }
  }

  def transApply[F[_, _], J](
    a: ArgIntro[F[○, *], J, K],
    trans: [k, l] => (k ->> l) => F[k, l],
    transApp: [j, k, l] => (k ->> l, ArgIntro[F[○, *], j, k]) => F[j, l],
  ): TypeExpr[F, J, L] =
    transApplyM[F, J, [x] =>> x](a, trans, transApp)

  def transApplyM[F[_, _], J, M[_]: Monad](
    a: ArgIntro[F[○, *], J, K],
    trans: [k, l] => (k ->> l) => F[k, l],
    transApp: [j, k, l] => (k ->> l, ArgIntro[F[○, *], j, k]) => M[F[j, l]],
  ): M[TypeExpr[F, J, L]] =
    a.inKind.properKind match {
      case Left(j_eq_○) =>
        j_eq_○.substituteContra[[j] =>> M[TypeExpr[F, j, L]]](
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
  ): M[TypeExpr[F, ○, L]] = {
    this match {
      case Pair() =>
        args match {
          case ArgIntro.IntroBoth(a1, a2) =>
            BiApp(Pair[F](), ArgIntro.unwrap(a1), ArgIntro.unwrap(a2)).pure[M]
          case other =>
            throw new NotImplementedError(s"$other")
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
        throw new NotImplementedError(s"Applying $other to $args")
    }
  }

  private def transApply1M[F[_, _], J: ProperKind, M[_]: Monad](
    args: ArgIntro[F[○, *], J, K],
    trans: [k, l] => (k ->> l) => F[k, l],
    transApp: [j, k, l] => (k ->> l, ArgIntro[F[○, *], j, k]) => M[F[j, l]],
  ): M[TypeExpr[F, J, L]] = {
    this match {
      case ComposeSnd(op, g) =>
        args match {
          case ArgIntro.IntroFst(a, f) =>
            import op.in1Kind
            transApp(g, f)
              .map(AppCompose(op.cast, ArgIntro.unwrap(a), _))
          case other =>
            throw new NotImplementedError(s"$other")
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
            throw new NotImplementedError(s"$other")
        }

      case other =>
        throw new NotImplementedError(s"Applying $other to $args")
    }
  }

  def transCompose[A[_, _], J](
    a: ArgTrans[A, J, K],
    trans: [k, l] => (k ->> l) => A[k, l],
    transComp: [j, k, l] => (k ->> l, ArgTrans[A, j, k]) => A[j, l],
  ): TypeExpr[A, J, L] =
    transComposeM[A, J, [x] =>> x](a, trans, transComp)

  def transComposeM[A[_, _], J, M[_]: Monad](
    a: ArgTrans[A, J, K],
    trans: [k, l] => (k ->> l) => A[k, l],
    transComp: [j, k, l] => (k ->> l, ArgTrans[A, j, k]) => M[A[j, l]],
  ): M[TypeExpr[A, J, L]] =
    a.inKind.properKind match {
      case Left(j_eq_○) =>
        j_eq_○.substituteContra[[j] =>> M[TypeExpr[A, j, L]]](
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
  ): M[TypeExpr[F, ○, L]] =
    this match {
      case PFix(p, e) =>
        p.applyToTrans(ArgTrans.introFst(f)) match {
          case Routing.AppTransRes(q, g) =>
            transApp(e, g)
              .map(Fix(q, _))
        }
      case AppSnd(op, b) =>
        f match {
          case ArgTrans.Wrap(a) =>
            BiApp(op.cast[F], a, trans(b)).pure[M]
          case other =>
            throw new NotImplementedError(s"$other")
        }
      case AppCompose(op, a, g) =>
        transApp(g, f)
          .map(BiApp(op.cast[F], trans(a), _))
      case other =>
        throw new NotImplementedError(s"$other")
    }

  private def transCompose1M[F[_, _], J: ProperKind, M[_]: Monad](
    f: ArgTrans[F, J, K],
    trans: [k, l] => (k ->> l) => F[k, l],
    transComp: [j, k, l] => (k ->> l, ArgTrans[F, j, k]) => M[F[j, l]],
  ): M[TypeExpr[F, J, L]] = {

    def goOp[K1, K2](
      op: BinaryOperator[->>, K1, K2, L],
      f: ArgTrans[F, J, K1 × K2],
    ): M[TypeExpr[F, J, L]] = {
      import op.in1Kind
      import op.in2Kind

      f match {
        case snd @ ArgTrans.Snd(f2) =>
          composeSnd(op.cast[F], ArgTrans.unwrap(f2))(using snd.in2Kind).pure[M]
        case ArgTrans.IntroFst(f1) =>
          AppFst(op.cast[F], ArgTrans.unwrap(f1)).pure[M]
        case other =>
          throw new NotImplementedError(s"$other")
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
            throw new NotImplementedError(s"$other")
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
            throw new NotImplementedError(s"$other")
        }
      case other =>
        throw new NotImplementedError(s"Composing $other after $f")
    }
  }
}

object TypeExpr {

  sealed abstract class BinaryOperator[->>[_, _], K1, K2, L](using
    k1: OutputKind[K1],
    k2: OutputKind[K2],
    l: OutputKind[L],
  ) extends TypeExpr[->>, K1 × K2, L] {
    given in1Kind: OutputKind[K1] = k1
    given in2Kind: OutputKind[K2] = k2

    def cast[F[_, _]]: BinaryOperator[F, K1, K2, L] =
      this match {
        case Pair() => Pair()
        case Sum()  => Sum()
        case RecCall() => RecCall()
      }
  }

  case class UnitType[->>[_, _]]() extends TypeExpr[->>, ○, ●]
  case class IntType[->>[_, _]]() extends TypeExpr[->>, ○, ●]
  case class StringType[->>[_, _]]() extends TypeExpr[->>, ○, ●]

  case class Pair[->>[_, _]]() extends BinaryOperator[->>, ●, ●, ●]
  case class Sum[->>[_, _]]() extends BinaryOperator[->>, ●, ●, ●]
  case class RecCall[->>[_, _]]() extends BinaryOperator[->>, ●, ●, ●]

  case class Fix[->>[_, _], K](f: Routing[●, K], g: K ->> ●) extends TypeExpr[->>, ○, ●]

  // TODO: Make the representation normalized (part of initial routing may possibly be factored out)
  case class PFix[->>[_, _], K, X](
    f: Routing[K × ●, X],
    g: X ->> ●,
  )(using
    val properInKind: ProperKind[K],
  ) extends TypeExpr[->>, K, ●]

  case class AbstractType[->>[_, _]](label: AbstractTypeLabel) extends TypeExpr[->>, ○, ●]

  case class ScalaTypeParam(filename: String, line: Int, name: String)
  case class ScalaTypeParams[->>[_, _]](values: Set[ScalaTypeParam]) extends TypeExpr[->>, ○, ●] {
    require(values.nonEmpty)
  }
  object ScalaTypeParams {
    def one[->>[_, _]](filename: String, line: Int, name: String): ScalaTypeParams[->>] =
      ScalaTypeParams(Set(ScalaTypeParam(filename, line, name)))
  }

  case class BiApp[->>[_, _], K1, K2, L](
    op: BinaryOperator[->>, K1, K2, L],
    arg1: ○ ->> K1,
    arg2: ○ ->> K2,
  ) extends TypeExpr[->>, ○, L](using summon, op.outKind)

  case class AppFst[->>[_, _], K1, K2, L](
    op: BinaryOperator[->>, K1, K2, L],
    arg1: ○ ->> K1,
  ) extends TypeExpr[->>, K2, L](using op.in2Kind.kind, op.outKind)

  case class AppSnd[->>[_, _], K1, K2, L](
    op: BinaryOperator[->>, K1, K2, L],
    arg2: ○ ->> K2,
  ) extends TypeExpr[->>, K1, L](using op.in1Kind.kind, op.outKind)

  case class ComposeSnd[->>[_, _], K1, K2: ProperKind, L2, M](
    op: BinaryOperator[->>, K1, L2, M],
    arg2: K2 ->> L2,
  ) extends TypeExpr[->>, K1 × K2, M](using
    (Kind.fst(op.inKind) × ProperKind[K2]).kind,
    op.outKind,
  )

  case class AppCompose[->>[_, _], K, L1, L2, M](
    op: BinaryOperator[->>, L1, L2, M],
    arg1: ○ ->> L1,
    arg2: K ->> L2,
  )(using
    val properInKind: ProperKind[K],
  ) extends TypeExpr[->>, K, M](using summon, op.outKind)

  case class TypeError[->>[_, _], K: Kind, L: OutputKind](msg: String) extends TypeExpr[->>, K, L]

  def abstractType[->>[_, _]](label: AbstractTypeLabel): TypeExpr[->>, ○, ●] =
    AbstractType(label)

  def pair[->>[_, _]](a: ○ ->> ●, b: ○ ->> ●): TypeExpr[->>, ○, ●] =
    BiApp(Pair(), a, b)

  def sum[->>[_, _]](a: ○ ->> ●, b: ○ ->> ●): TypeExpr[->>, ○, ●] =
    BiApp(Sum(), a, b)

  def recCall[->>[_, _]](a: ○ ->> ●, b: ○ ->> ●): TypeExpr[->>, ○, ●] =
    BiApp(RecCall(), a, b)

  def pair1[->>[_, _]](a: ○ ->> ●): TypeExpr[->>, ●, ●] =
    AppFst(Pair(), a)

  def pair2[->>[_, _]](b: ○ ->> ●): TypeExpr[->>, ●, ●] =
    AppSnd(Pair(), b)

  def sum1[->>[_, _]](a: ○ ->> ●): TypeExpr[->>, ●, ●] =
    AppFst(Sum(), a)

  def sum2[->>[_, _]](b: ○ ->> ●): TypeExpr[->>, ●, ●] =
    AppSnd(Sum(), b)

  def appCompose[->>[_, _], K, L1, L2, M](
    op: BinaryOperator[->>, L1, L2, M],
    arg1: ○ ->> L1,
    arg2: K ->> L2,
  )(using
    k: ProperKind[K],
  ): TypeExpr[->>, K, M] =
    AppCompose(op, arg1, arg2)

  def composeSnd[->>[_, _], K1, K2: ProperKind, L2, M](
    op: BinaryOperator[->>, K1, L2, M],
    arg2: K2 ->> L2,
  ): TypeExpr[->>, K1 × K2, M] =
    ComposeSnd(op, arg2)

}
