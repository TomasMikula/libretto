package libretto.typology.types

import libretto.lambda.{MappedMorphism, MonoidalCategory, MonoidalObjectMap, Semigroupoid, Unzippable}
import libretto.lambda.util.{Exists, TypeEq}
import libretto.lambda.util.TypeEq.Refl
import libretto.typology.kinds.*

/**
 * Tree-shaped structure that builds up a type
 * (or type constructor, depending on the output kind `L`),
 * from primitive, language specific type constructors.
 *
 * When the input kind `K` is the unit kind [[○]], then this [[TypeExpr]]
 * represents a fully formed type. Otherwise, it represents a type constructor
 * taking additional type parameters of kinds `K`.
 *
 * @tparam TC the primitive, language-specific type constructors, parameterized by input and output kinds
 * @tparam K the kind of additional type parameters of the represented type constructor
 * @tparam L the output kind of the represented type constructor
 */
sealed abstract class TypeExpr[TC[_, _], K, L](using
  val inKind: Kinds[K],
  val outKind: Kind[L],
) {
  import TypeExpr.*

  def from[J](using ev: J =:= K): TypeExpr[TC, J, L] =
    ev.substituteContra[TypeExpr[TC, _, L]](this)

  def to[M](using ev: L =:= M): TypeExpr[TC, K, M] =
    ev.substituteCo[TypeExpr[TC, K, _]](this)

  def >[M](that: TypeExpr[TC, L, M]): TypeExpr[TC, K, M] =
    that ∘ this

  def ∘[J](that: TypeExpr[TC, J, K]): TypeExpr[TC, J, L] =
    import that.given
    applyTo(PartialArgs(that))

  def after(that: TypeExpr[TC, ○, K]): TypeExpr[TC, ○, L] =
    this ∘ that

  def applyTo[J](
    a: PartialArgs[TypeExpr[TC, _, _], J, K],
  ): TypeExpr[TC, J, L] =
    this match {
      case Primitive(p) =>
        App(p, a)
      case App(op, b) =>
        App(op, (a > b)(absorbArgs[TC]))
    }

  def translate[TC1[_, _]](
    f: [k, l] => TC[k, l] => TC1[k, l]
  ): TypeExpr[TC1, K, L] =
    this match {
      case Primitive(p) =>
        Primitive(f(p))
      case App(op, args) =>
        App(
          f(op),
          args.translate([x, y] => (t: TypeExpr[TC, x, y]) => t.translate(f)),
        )
    }

  def compile[==>[_, _], <*>[_, _], One, F[_, _], Q](
    fk: F[K, Q],
    compilePrimitive: [k, l, q] => (F[k, q], TC[k, l]) => MappedMorphism[==>, F, k, l],
  )(using
    tgt: MonoidalCategory[==>, <*>, One],
    F: MonoidalObjectMap[F, ×, ○, <*>, One],
  ): MappedMorphism[==>, F, K, L] = {

    val go = [k, l, q] => (fkq: F[k, q], t: TypeExpr[TC, k, l]) => {
      val t1 = t.compile[==>, <*>, One, F, q](fkq, compilePrimitive)
      Exists[[r] =>> (q ==> r, F[l, r]), t1.FB]((t1.get(fkq, t1.tgtMap), t1.tgtMap))
    }

    this match
      case Primitive(op) =>
        compilePrimitive(fk, op)
      case App(op, args) =>
        args.foldTranslate[==>, <*>, One, F, Q](F.unit, fk, go) match {
          case Exists.Some((args, fx)) =>
            val op1 = compilePrimitive(fx, op)
            MappedMorphism(fk, args > op1.get(fx, op1.tgtMap), op1.tgtMap)
        }
  }

  private def absorbArgs[TC[_, _]] =
    [j, k, l] => (
      a: PartialArgs[TypeExpr[TC, _, _], j, k],
      t: TypeExpr[TC, k, l],
    ) => {
      t.applyTo(a)
    }
}

object TypeExpr {

  case class Primitive[TC[_, _], L](
    value: TC[○, L],
  )(using
    Kind[L],
  ) extends TypeExpr[TC, ○, L]

  case class App[TC[_, _], K, L, M](
    f: TC[L, M],
    args: PartialArgs[TypeExpr[TC, _, _], K, L],
  )(using
    Kind[M],
  ) extends TypeExpr[TC, K, M](using args.inKind)

  def lift[TC[_, _], K, L](f: TC[K, L])(using
    Kinds[K],
    Kind[L],
  ): TypeExpr[TC, K, L] =
    Kinds[K].nonEmpty match
      case Left(TypeEq(Refl())) => Primitive(f)
      case Right(k) => App(f, PartialArgs.Id()(using k))

  given semigroupoid[TC[_, _]]: Semigroupoid[TypeExpr[TC, _, _]] with {
    override def andThen[A, B, C](
      f: TypeExpr[TC, A, B],
      g: TypeExpr[TC, B, C],
    ): TypeExpr[TC, A, C] =
      f > g
  }

  given unzippable[TC[_, _]]: Unzippable[×, TypeExpr[TC, ○, _]] with {
    override def unzip[A, B](
      ab: TypeExpr[TC, ○, A × B],
    ): (TypeExpr[TC, ○, A], TypeExpr[TC, ○, B]) =
      Kind.cannotBePair(ab.outKind)
  }
}