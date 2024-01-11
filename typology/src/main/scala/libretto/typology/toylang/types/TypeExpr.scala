package libretto.typology.toylang.types

import libretto.lambda.{MappedMorphism, MonoidalObjectMap, SemigroupalCategory, Semigroupoid, Tupled, UnhandledCase}
import libretto.lambda.util.{Exists, Monad, SourcePos, TypeEq}
import libretto.lambda.util.TypeEq.Refl
import libretto.lambda.util.Monad.syntax._
import libretto.typology.kinds._
import libretto.lambda.Unzippable

/**
 * Tree-like structure that builds up a type
 * (or type constructor, depending on the output kind `L`).
 *
 * May take type parameters, represented by the input kind `K`.
 *
 * Goal (not quite there yet):
 * Each type (constructor) has a unique representation as [[TypeExpr]]
 * (i.e. each [[TypeExpr]] is a normal form).
 *
 * @tparam V labeling of type variables
 */
sealed abstract class TypeExpr[V, K, L](using
  val inKind: Kind[K],
  val outKind: OutputKind[L],
) {
  import TypeExpr.*

  def from[J](using ev: J =:= K): TypeExpr[V, J, L] =
    ev.substituteContra[TypeExpr[V, _, L]](this)

  def to[M](using ev: L =:= M): TypeExpr[V, K, M] =
    ev.substituteCo[TypeExpr[V, K, _]](this)

  def >[M](that: TypeExpr[V, L, M]): TypeExpr[V, K, M] =
    that ∘ this

  def ∘[J](that: TypeExpr[V, J, K]): TypeExpr[V, J, L] =
    import that.given
    applyTo(PartialArgs(that))

  def after(that: TypeExpr[V, ○, K]): TypeExpr[V, ○, L] =
    this ∘ that

  def applyTo[J](
    a: PartialArgs[TypeExpr[V, _, _], J, K],
  ): TypeExpr[V, J, L] =
    a.inKind.properKind match {
      case Left(TypeEq(Refl())) => applyTo0(a)
      case Right(j)             => applyTo1(a)(using j)
    }

  private def applyTo0(
    f: PartialArgs[TypeExpr[V, _, _], ○, K],
  ): TypeExpr[V, ○, L] =
    this match {
      case Wrap(p) =>
        App(p, f)
      case App(op, g) =>
        App(op, (f > g)(TypeExpr.absorbArgs[V]))
      case other =>
        throw new NotImplementedError(s"$other (${summon[SourcePos]})")
    }

  private def applyTo1[J: ProperKind](
    f: PartialArgs[TypeExpr[V, _, _], J, K],
  ): TypeExpr[V, J, L] =
    this match {
      case App(op, g) =>
        val h = (f > g)(absorbL = TypeExpr.absorbArgs[V])
        App(op, h)
      case Wrap(op) =>
        App(op, f)
      case other =>
        throw new NotImplementedError(s"Composing $other after $f (${summon[SourcePos]})")
    }

  def compile[==>[_, _], F[_, _], Q](
    tgt: TypeAlgebra[V, ==>],
    fk: F[K, Q],
    map_● : F[●, tgt.Type],
  )(using
    F: MonoidalObjectMap[F, ×, ○, tgt.<*>, tgt.None],
  ): MappedMorphism[==>, F, K, L] =
    compile(
      tgt,
      fk,
      map_●,
      compilePrimitive =
        [k, l, q] => (fk: F[k, q], p: Primitive[V, k, l]) => {
          import Primitive.*
          p match
            case UnitType() =>
              MappedMorphism(F.unit, tgt.unit, map_●)
            case IntType() =>
              MappedMorphism(F.unit, tgt.int, map_●)
            case StringType() =>
              MappedMorphism(F.unit, tgt.string, map_●)
            case Pair() =>
              MappedMorphism(F.pair(map_●, map_●), tgt.pair, map_●)
            case Sum() =>
              MappedMorphism(F.pair(map_●, map_●), tgt.sum, map_●)
            case RecCall() =>
              MappedMorphism(F.pair(map_●, map_●), tgt.recCall, map_●)
            case Fix(f, g) =>
              MappedMorphism(F.unit, tgt.fix(TypeFun(f, g)), map_●)
            case PFix(f, g) =>
              MappedMorphism(map_●, tgt.pfix(TypeFun(f, g)), map_●)
            case AbstractType(label) =>
              MappedMorphism(F.unit, tgt.abstractTypeName(label), map_●)
            case TypeMismatch(a, b) =>
              throw NotImplementedError(s"TypeMismatch($a, $b) at ${summon[SourcePos]}")
            case ForbiddenSelfRef(v) =>
              throw NotImplementedError(s"ForbiddenSelfReference($v) at ${summon[SourcePos]}")
        },
    )

  def compile[==>[_, _], F[_, _], Q](
    tgt: TypeAlgebra[V, ==>],
    fk: F[K, Q],
    map_● : F[●, tgt.Type],
    compilePrimitive: [k, l, q] => (F[k, q], Primitive[V, k, l]) => MappedMorphism[==>, F, k, l],
  )(using
    F: MonoidalObjectMap[F, ×, ○, tgt.<*>, tgt.None],
  ): MappedMorphism[==>, F, K, L] = {
    import tgt.given

    val go = [k, l, q] => (fkq: F[k, q], t: TypeExpr[V, k, l]) => {
      val t1 = t.compile[==>, F, q](tgt, fkq, map_●, compilePrimitive)
      Exists[[r] =>> (q ==> r, F[l, r]), t1.FB]((t1.get(fkq, t1.tgtMap), t1.tgtMap))
    }

    this match
      case Wrap(op) =>
        compilePrimitive(fk, op)
      case App(op, args) =>
        args.foldTranslate[==>, tgt.<*>, tgt.None, F, Q](F.unit, fk, go) match {
          case Exists.Some((args, fx)) =>
            val op1 = compilePrimitive(fx, op)
            MappedMorphism(fk, args > op1.get(fx, op1.tgtMap), op1.tgtMap)
        }
  }

  def vmap[W](f: V => W): TypeExpr[W, K, L] =
    this match {
      case Wrap(p) =>
        Wrap(p.vmap(f))
      case App(op, args) =>
        App(
          op.vmap(f),
          args.translate([x, y] => (t: TypeExpr[V, x, y]) => t.vmap(f)),
        )
    }
}

object TypeExpr {
  sealed trait Primitive[V, K, L](using
    val inKind: Kind[K],
    val outKind: OutputKind[L],
  ) {
    import Primitive.*

    def vmap[W](f: V => W): Primitive[W, K, L] =
      this match
        case AbstractType(label) => AbstractType(f(label))
        case Fix(g, h)           => Fix(g, h.vmap(f))
        case x @ PFix(g, h)      => import x.given; PFix(g, h.vmap(f))
        case UnitType()          => UnitType()
        case IntType()           => IntType()
        case StringType()        => StringType()
        case Pair()              => Pair()
        case Sum()               => Sum()
        case RecCall()           => RecCall()
        case RecCall()           => RecCall()
        case TypeMismatch(a, b)  => TypeMismatch(a.vmap(f), b.vmap(f))
        case ForbiddenSelfRef(v) => ForbiddenSelfRef(f(v))

  }

  object Primitive {
    case class AbstractType[V](label: V) extends Primitive[V, ○, ●]

    case class UnitType[V]() extends Primitive[V, ○, ●]
    case class IntType[V]() extends Primitive[V, ○, ●]
    case class StringType[V]() extends Primitive[V, ○, ●]

    case class Pair[V]() extends Primitive[V, ● × ●, ●]
    case class Sum[V]() extends Primitive[V, ● × ●, ●]
    case class RecCall[V]() extends Primitive[V, ● × ●, ●]

    case class Fix[V, K](
      f: Routing[●, K],
      g: TypeExpr[V, K, ●],
    ) extends Primitive[V, ○, ●]

    // TODO: Make the representation normalized (part of initial routing may possibly be factored out)
    case class PFix[V, X](
      f: Routing[● × ●, X],
      g: TypeExpr[V, X, ●],
    ) extends Primitive[V, ●, ●]

    case class TypeMismatch[V, K: Kind, L: OutputKind](
      a: TypeExpr[V, K, L],
      b: TypeExpr[V, K, L],
    ) extends Primitive[V, K, L]

    case class ForbiddenSelfRef[V, K: Kind, L: OutputKind](
      v: V,
    ) extends Primitive[V, K, L]
  }

  case class Wrap[V, K, L](value: Primitive[V, K, L]) extends TypeExpr[V, K, L](using
    value.inKind,
    value.outKind,
  )

  case class App[V, K, L, M](
    f: Primitive[V, L, M],
    args: PartialArgs[TypeExpr[V, _, _], K, L],
  ) extends TypeExpr[V, K, M](using args.inKind, f.outKind)

  def abstractType[V](label: V): TypeExpr[V, ○, ●] =
    Wrap(Primitive.AbstractType(label))

  def pair[V]: TypeExpr[V, ● × ●, ●] =
    Wrap(Primitive.Pair())

  def pair[V](a: TypeExpr[V, ○, ●], b: TypeExpr[V, ○, ●]): TypeExpr[V, ○, ●] =
    App(Primitive.Pair(), PartialArgs.introBoth(PartialArgs(a), PartialArgs(b)))

  def pair1[V](a: TypeExpr[V, ○, ●]): TypeExpr[V, ●, ●] =
    App(Primitive.Pair(), PartialArgs.introFst(PartialArgs(a)))

  def pair2[V](b: TypeExpr[V, ○, ●]): TypeExpr[V, ●, ●] =
    App(Primitive.Pair(), PartialArgs.introSnd(PartialArgs(b)))

  def sum[V]: TypeExpr[V, ● × ●, ●] =
    Wrap(Primitive.Sum())

  def sum[V](a: TypeExpr[V, ○, ●], b: TypeExpr[V, ○, ●]): TypeExpr[V, ○, ●] =
    App(Primitive.Sum(), PartialArgs.introBoth(PartialArgs(a), PartialArgs(b)))

  def sum1[V](a: TypeExpr[V, ○, ●]): TypeExpr[V, ●, ●] =
    App(Primitive.Sum(), PartialArgs.introFst(PartialArgs(a)))

  def sum2[V](b: TypeExpr[V, ○, ●]): TypeExpr[V, ●, ●] =
    App(Primitive.Sum(), PartialArgs.introSnd(PartialArgs(b)))

  def recCall[V](a: TypeExpr[V, ○, ●], b: TypeExpr[V, ○, ●]): TypeExpr[V, ○, ●] =
    App(Primitive.RecCall(), PartialArgs.introBoth(PartialArgs(a), PartialArgs(b)))

  def fix[V, K](f: Routing[●, K], g: TypeExpr[V, K, ●]): TypeExpr[V, ○, ●] =
    Wrap(Primitive.Fix(f, g))

  def pfix[V, X](f: Routing[● × ●, X], g: TypeExpr[V, X, ●]): TypeExpr[V, ●, ●] =
    Wrap(Primitive.PFix(f, g))

  def typeMismatch[V, K: Kind, L: OutputKind](
    a: TypeExpr[V, K, L],
    b: TypeExpr[V, K, L],
  ): TypeExpr[V, K, L] =
    Wrap(Primitive.TypeMismatch(a, b))

  def forbiddenSelfReference[V, K: Kind, L: OutputKind](
    v: V,
  ): TypeExpr[V, K, L] =
    Wrap(Primitive.ForbiddenSelfRef(v))

  def unit[V]: TypeExpr[V, ○, ●] =
    Wrap(Primitive.UnitType())

  def int[V]: TypeExpr[V, ○, ●] =
    Wrap(Primitive.IntType())

  def string[V]: TypeExpr[V, ○, ●] =
    Wrap(Primitive.StringType())

  given semigroupoid[V]: Semigroupoid[TypeExpr[V, _, _]] with {
    override def andThen[A, B, C](
      f: TypeExpr[V, A, B],
      g: TypeExpr[V, B, C],
    ): TypeExpr[V, A, C] =
      f > g
  }

  given unzippable[V]: Unzippable[×, TypeExpr[V, ○, _]] with {
    override def unzip[A, B](
      ab: TypeExpr[V, ○, A × B],
    ): (TypeExpr[V, ○, A], TypeExpr[V, ○, B]) =
      OutputKind.cannotBePair(ab.outKind)
  }

  private def absorbArgs[V] =
    [j, k, l] => (
      a: PartialArgs[TypeExpr[V, _, _], j, k],
      t: TypeExpr[V, k, l],
    ) => {
      t.applyTo(a)
    }
}
