package libretto.lambda

import libretto.lambda.util.{Functional, TypeEq}
import libretto.lambda.util.TypeEq.Refl

/** Image of some morphism `A -> B` in the target category `->>`.
 *
 * @tparam ->> target category
 * @tparam F   mapping of objects.
 *             `F[A, X]` is evidence that object `A` of the source category
 *             is mapped to object `X` of the target category.
 * @tparam A source of the original morphism in the source category
 * @tparam B target of the original morphism in the source category
 */
trait MappedMorphism[->>[_, _], F[_, _], A, B] {
  /** Source of the mapped morphism. Object of the target category. */
  type FA

  /** Target of the mapped morphism. Object of the target category. */
  type FB

  /** Evidence that the source `FA` of the mapped morphism is the image of the source `A` of the original morphism. */
  val srcMap: F[A, FA]

  /** Evidence that the target `FB` of the mapped morphism is the image of the target `B` of the original morphism. */
  val tgtMap: F[B, FB]

  /** The mapped morphism. */
  val ff: FA ->> FB

  def get[X, Y](fx: F[A, X], fy: F[B, Y])(using F: Functional[F]): X ->> Y =
    F.uniqueOutputType(srcMap, fx) match
      case TypeEq(Refl()) =>
        F.uniqueOutputType(tgtMap, fy) match
          case TypeEq(Refl()) =>
            ff

  def >[C](that: MappedMorphism[->>, F, B, C])(using
    F: Functional[F],
    cat: Semigroupoid[->>],
  ): MappedMorphism[->>,F, A, C] = {
    given (this.FB =:= that.FA) =
      F.uniqueOutputType(this.tgtMap, that.srcMap)

    MappedMorphism(
      this.srcMap,
      this.ff.to[that.FA] > that.ff,
      that.tgtMap,
    )
  }
}

object MappedMorphism {
  def apply[->>[_, _], F[_, _], X, Y, FX, FY](
    fx: F[X, FX],
    g: FX ->> FY,
    fy: F[Y, FY],
  ): MappedMorphism[->>, F, X, Y] =
    new MappedMorphism[->>, F, X, Y] {
      override type FA = FX
      override type FB = FY
      override val srcMap: F[X, FX] = fx
      override val tgtMap: F[Y, FY] = fy
      override val ff: FX ->> FY = g
    }

  def par[->>[_, _], F[_, _], <*>[_, _], |*|[_, _], A1, A2, B1, B2](
    f1: MappedMorphism[->>, F, A1, B1],
    f2: MappedMorphism[->>, F, A2, B2],
  )(using
    F: SemigroupalObjectMap[<*>, |*|, F],
    cat: SemigroupalCategory[->>, |*|],
  ): MappedMorphism[->>, F, A1 <*> A2, B1 <*> B2] =
    MappedMorphism(
      F.pair(f1.srcMap, f2.srcMap),
      cat.par(f1.ff, f2.ff),
      F.pair(f1.tgtMap, f2.tgtMap),
    )

  def composeFst[->>[_, _], F[_, _], <*>[_, _], |*|[_, _], A1, A2, B, Z1](
    h: MappedMorphism[->>, F, A1 <*> A2, B],
    g1: MappedMorphism[->>, F, Z1, A1],
  )(using
    F: SemigroupalObjectMap[<*>, |*|, F],
    cat: SemigroupalCategory[->>, |*|],
  ): MappedMorphism[->>, F, Z1 <*> A2, B] = {
    val f12 = F.unpair(h.srcMap)
    import f12.f2
    par(
      g1,
      MappedMorphism(f2, cat.id, f2),
    ) > h
  }

  def composeSnd[->>[_, _], F[_, _], <*>[_, _], |*|[_, _], A1, A2, B, Z2](
    h: MappedMorphism[->>, F, A1 <*> A2, B],
    g2: MappedMorphism[->>, F, Z2, A2],
  )(using
    F: SemigroupalObjectMap[<*>, |*|, F],
    cat: SemigroupalCategory[->>, |*|],
  ): MappedMorphism[->>, F, A1 <*> Z2, B] = {
    val f12 = F.unpair(h.srcMap)
    import f12.f1
    par(
      MappedMorphism(f1, cat.id, f1),
      g2,
    ) > h
  }

  def composeIntroFst[->>[_, _], F[_, _], <*>[_, _], |*|[_, _], One, Unit, A2, B](
    h: MappedMorphism[->>, F, One <*> A2, B],
  )(using
    F: MonoidalObjectMap[F, <*>, One, |*|, Unit],
    cat: MonoidalCategory[->>, |*|, Unit],
  ): MappedMorphism[->>, F, A2, B] = {
    val f12 = F.unpair(h.srcMap)
    import f12.{f1, f2}
    F.uniqueOutputType(f1, F.unit) match {
      case TypeEq(Refl()) =>
        MappedMorphism(f2, cat.introFst, F.pair(f1, f2)) > h
    }
  }

  def composeIntroSnd[->>[_, _], F[_, _], <*>[_, _], |*|[_, _], One, Unit, A1, B](
    h: MappedMorphism[->>, F, A1 <*> One, B],
  )(using
    F: MonoidalObjectMap[F, <*>, One, |*|, Unit],
    cat: MonoidalCategory[->>, |*|, Unit],
  ): MappedMorphism[->>, F, A1, B] = {
    val f12 = F.unpair(h.srcMap)
    import f12.{f1, f2}
    F.uniqueOutputType(f2, F.unit) match {
      case TypeEq(Refl()) =>
        MappedMorphism(f1, cat.introSnd, F.pair(f1, f2)) > h
    }
  }
}
