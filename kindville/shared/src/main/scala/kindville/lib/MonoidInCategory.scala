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
case class MonoidInCategory[K, Obj <: AnyKind, -> <: AnyKind, × <: AnyKind, One <: AnyKind, M <: AnyKind](
  obj: App[K, Obj, M],
  unitKImpl: Arrow[K, ->, One, M],
  combineKImpl: Box[MonoidInCategory.CombineCode[K], -> :: × :: M :: TNil],
) {
  transparent inline def unitK =
    decodeT[Obj :: -> :: × :: One :: M :: TNil]:
      [⋅⋅[_]] => kuotes ?=> [
        Obj[_ <: ⋅⋅[K]],
        ->[_ <: ⋅⋅[K], _ <: ⋅⋅[K]],
        × <: [_ <: ⋅⋅[K], _ <: ⋅⋅[K]] =>> ⋅⋅[K],
        One <: ⋅⋅[K],
        M <: ⋅⋅[K],
      ] => () =>
        val m: One -> M = kuotes.splice(this.unitKImpl.unpack)
        m

  transparent inline def combineK =
    decodeT[Obj :: -> :: × :: One :: M :: TNil]:
      [⋅⋅[_]] => kuotes ?=> [
        Obj[_ <: ⋅⋅[K]],
        ->[_ <: ⋅⋅[K], _ <: ⋅⋅[K]],
        × <: [_ <: ⋅⋅[K], _ <: ⋅⋅[K]] =>> ⋅⋅[K],
        One <: ⋅⋅[K],
        M <: ⋅⋅[K],
      ] => () =>
        val m: (M × M) -> M = kuotes.splice(this.combineKImpl.unpack)
        m
}

object MonoidInCategory {
  type CombineCode[K] =
    [⋅⋅[_]] =>> [
      ->[_ <: ⋅⋅[K], _ <: ⋅⋅[K]],
      × <: [_ <: ⋅⋅[K], _ <: ⋅⋅[K]] =>> ⋅⋅[K],
      M <: ⋅⋅[K],
    ] =>>
      (M × M) -> M
}

type ~>[F[_], G[_]] = [A] => F[A] => G[A]
type Id[A] = A
type ∘[F[_], G[_]] = [A] =>> F[G[A]]
type Const[A] = [X] =>> A
type ConstF[A] = [F[_]] =>> A

trait Functor[F[_]] {
  def map[A, B](f: A => B): F[A] => F[B]
}

sealed trait Day[F[_], G[_], A]:
  type X
  type Y
  def fx: F[X]
  def gy: G[Y]
  def f: (X, Y) => A

object Day:
  private case class DayImpl[F[_], G[_], A, X0, Y0](fx: F[X0], gy: G[Y0], f: (X0, Y0) => A) extends Day[F, G, A] {
    override type X = X0
    override type Y = Y0
  }

  def apply[F[_], G[_], A, X, Y](fx: F[X], gy: G[Y], f: (X, Y) => A): Day[F, G, A] =
    DayImpl(fx, gy, f)

type DayConv[F[_], G[_]] = [A] =>> Day[F, G, A]

// normally we would make these traits, but here we want to emphasize they are *just* monoids
opaque type Monoid[M]         = MonoidInCategory[     ●, Const[Unit] , _ => _, (_, _) , Unit, M]
opaque type Monad [M[_]]      = MonoidInCategory[● -> ●, Functor     ,   ~>  ,   ∘    , Id  , M]
opaque type Applicative[F[_]] = MonoidInCategory[● -> ●, ConstF[Unit],   ~>  , DayConv, Id  , F]

object Monoid {
  def apply[M](
    unit: M,
    combine: (M, M) => M,
  ): Monoid[M] =
    MonoidInCategory[●, Const[Unit], _ => _, (_, _), Unit, M](
      App.packer[●][Const[Unit], M](()),
      Arrow.packer[●][_ => _, Unit, M]((_: Unit) => unit),
      Box.packer[MonoidInCategory.CombineCode[●]][_ => _, (_, _), M](combine.tupled),
    )

  extension [M](self: Monoid[M]) {
    inline def unit(x: Unit): M =
      self.unitK
        .typecheckAs[Unit => M]
        .apply(x)

    inline def combine(x: M, y: M): M =
      self.combineK
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
    MonoidInCategory[● -> ●, Functor, ~>, ∘, Id, M](
      App.packer[● -> ●][Functor, M](functor),
      Arrow.packer[● -> ●][~>, Id, M](pure),
      Box.packer[MonoidInCategory.CombineCode[● -> ●]][~>, ∘, M](flatten),
    )

  extension [M[_]](self: Monad[M]) {
    inline def pure[A](a: A): M[A] =
      self.unitK
        .typecheckAs[Id ~> M]
        .apply[A](a)

    inline def flatten[A](mma: M[M[A]]): M[A] =
      self.combineK
        .typecheckAs[(M ∘ M) ~> M]
        .apply[A](mma)
  }
}

object Applicative {
  def apply[F[_]](
    pure: Id ~> F,
    ap: DayConv[F, F] ~> F,
  ): Applicative[F] =
    MonoidInCategory[● -> ●, ConstF[Unit], ~>, DayConv, Id, F](
      App.packer[● -> ●][ConstF[Unit], F](()),
      Arrow.packer[● -> ●][~>, Id, F](pure),
      Box.packer[MonoidInCategory.CombineCode[● -> ●]][~>, DayConv, F](ap),
    )

  extension [F[_]](self: Applicative[F]) {
    inline def pure[A](a: A): F[A] =
      self.unitK
        .typecheckAs[Id ~> F]
        .apply[A](a)

    inline def ap[A, B](fab: F[A => B], fa: F[A]): F[B] =
      self.combineK
        .typecheckAs[DayConv[F, F] ~> F]
        .apply[B](Day(fab, fa, (f, a) => f(a)))

    inline def map[A, B](fa: F[A])(f: A => B): F[B] =
      ap(pure(f), fa)
  }
}
