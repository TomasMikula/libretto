package kindville.lib

import kindville.{`*` as ●, *}
import kindville.Box.*

/** `M` is a monoid object in the monoidal category whose
 *
 * - objects are Scala types `A` of kind `K` for which there exists evidence `Obj[A]`;
 * - morphisms are values `A -> B`;
 * - monoidal product is `×`;
 * - monoidal unit is `One`.
 */
opaque type MonoidInCategory[K, Obj <: AnyKind, -> <: AnyKind, × <: AnyKind, One <: AnyKind, M <: AnyKind] =
  Box[MonoidInCategory.Code[K], -> :: × :: One :: M :: TNil]

object MonoidInCategory {
  type Code[K] =
    [⋅⋅[_]] =>> [
      Obj[_ <: ⋅⋅[K]],
      ->[_ <: ⋅⋅[K], _ <: ⋅⋅[K]],
      × <: [_ <: ⋅⋅[K], _ <: ⋅⋅[K]] =>> ⋅⋅[K], // TODO: support ⋅⋅[K] in this position
      One <: ⋅⋅[K],
      M <: ⋅⋅[K],
    ] =>> (
      obj: Obj[M],
      unit: One -> M,
      combine: (M × M) -> M,
    )

  transparent inline def apply[K] =
    Box.packer[Code[K]]

  extension [K, Obj <: AnyKind, -> <: AnyKind, × <: AnyKind, One <: AnyKind, M <: AnyKind](self: MonoidInCategory[K, Obj, ->, ×, One, M]) {
    transparent inline def unit =
      decodeT[Obj :: -> :: × :: One :: M :: TNil]:
        [⋅⋅[_]] => kuotes ?=> [
          Obj[_ <: ⋅⋅[K]],
          ->[_ <: ⋅⋅[K], _ <: ⋅⋅[K]],
          × <: [_ <: ⋅⋅[K], _ <: ⋅⋅[K]] =>> ⋅⋅[K],
          One <: ⋅⋅[K],
          M <: ⋅⋅[K],
        ] => () =>
          val m: (obj: Obj[M], unit: One -> M, combine: (M × M) -> M) =
            kuotes.splice(self.unpack)
          m.unit

    transparent inline def combine =
      decodeT[-> :: × :: One :: M :: TNil]:
        [⋅⋅[_]] => kuotes ?=> [
          ->[_ <: ⋅⋅[K], _ <: ⋅⋅[K]],
          × <: [_ <: ⋅⋅[K], _ <: ⋅⋅[K]] =>> ⋅⋅[K],
          One <: ⋅⋅[K],
          M <: ⋅⋅[K],
        ] => () =>
          val m: (unit: One -> M, combine: (M × M) -> M) =
            kuotes.splice(self.unpack)
          m.combine
  }
}

type ~>[F[_], G[_]] = [A] => F[A] => G[A]
type Id[A] = A
type ∘[F[_], G[_]] = [A] =>> F[G[A]]
type Const[A] = [X] =>> A

trait Functor[F[_]] {
  def map[A, B](f: A => B): F[A] => F[B]
}

opaque type Monoid[M]    = MonoidInCategory[     ●, Const[Unit], _ => _, (_, _), Unit, M]
opaque type Monad [M[_]] = MonoidInCategory[● -> ●, Functor    ,   ~>  ,   ∘   , Id  , M]

object Monoid {
  def apply[M](
    unit: M,
    combine: (M, M) => M,
  ): Monoid[M] =
    MonoidInCategory[●][Const[Unit], _ => _, (_, _), Unit, M](((), unit, combine))
}

object Monad {
  def apply[M[_]](
    functor: Functor[M],
    pure: Id ~> M,
    flatten: (M ∘ M) ~> M,
  ): Monad[M] =
    MonoidInCategory[● -> ●][Functor, ~>, ∘, Id, M]((functor, pure, flatten))
}
