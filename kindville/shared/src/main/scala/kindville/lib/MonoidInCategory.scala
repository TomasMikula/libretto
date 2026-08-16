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
  Box[MonoidInCategory.Code[K], Obj :: -> :: × :: One :: M :: TNil]

object MonoidInCategory {
  type Code[K] =
    [⋅⋅[_]] =>> [
      Obj[_ <: ⋅⋅[K]],
      ->[_ <: ⋅⋅[K], _ <: ⋅⋅[K]],
      × <: [_ <: ⋅⋅[K], _ <: ⋅⋅[K]] =>> ⋅⋅[K],
      One <: ⋅⋅[K],
      M <: ⋅⋅[K],
    ] =>>
      (Obj[M], One -> M, (M × M) -> M)

  transparent inline def apply[K] =
    decode:
      [⋅⋅[_]] => k ?=>
        val packer: [
          Obj[_ <: ⋅⋅[K]],
          ->[_ <: ⋅⋅[K], _ <: ⋅⋅[K]],
          × <: [_ <: ⋅⋅[K], _ <: ⋅⋅[K]] =>> ⋅⋅[K],
          One <: ⋅⋅[K],
          M <: ⋅⋅[K],
        ] => ((Obj[M], One -> M, (M × M) -> M)) => MonoidInCategory[K, Obj, ->, ×, ⋅⋅[One], ⋅⋅[M]] =
          k.splice(Box.packer[Code[K]])
        packer

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
          val m: (Obj[M], One -> M, (M × M) -> M) =
            kuotes.splice(self.unpack)
          m._2

    transparent inline def combine =
      decodeT[Obj :: -> :: × :: One :: M :: TNil]:
        [⋅⋅[_]] => kuotes ?=> [
          Obj[_ <: ⋅⋅[K]],
          ->[_ <: ⋅⋅[K], _ <: ⋅⋅[K]],
          × <: [_ <: ⋅⋅[K], _ <: ⋅⋅[K]] =>> ⋅⋅[K],
          One <: ⋅⋅[K],
          M <: ⋅⋅[K],
        ] => () =>
          val m: (Obj[M], One -> M, (M × M) -> M) =
            kuotes.splice(self.unpack)
          m._3
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
    MonoidInCategory.apply[●][Const[Unit], _ => _, (_, _), Unit, M](((), (_: Unit) => unit, combine.tupled))

  extension [M](self: Monoid[M]) {
    inline def unit(x: Unit): M =
      MonoidInCategory.unit(self)
        .typecheckAs[Unit => M]
        .apply(x)

    inline def combine(x: M, y: M): M =
      MonoidInCategory.combine(self)
        .typecheckAs[((M, M)) => M]
        .apply((x, y))
  }
}

object Monad {
  def apply[M[_]](
    functor: Functor[M],
    pure: Id ~> M,
    flatten: (M ∘ M) ~> M,
  ): Monad[M] =
    MonoidInCategory.apply[● -> ●][Functor, ~>, ∘, Id, M]((functor, pure, flatten))

  extension [M[_]](self: Monad[M]) {
    inline def pure[A](a: A): M[A] =
      MonoidInCategory.unit(self)
        .typecheckAs[Id ~> M]
        .apply[A](a)

    inline def flatten[A](mma: M[M[A]]): M[A] =
      MonoidInCategory.combine(self)
        .typecheckAs[(M ∘ M) ~> M]
        .apply[A](mma)
  }
}
