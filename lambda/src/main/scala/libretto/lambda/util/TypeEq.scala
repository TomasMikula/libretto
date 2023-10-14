package libretto.lambda.util

/** Type equality that, unlike Scala's `=:=`, can be pattern matched on. */
sealed trait TypeEq[A, B]

object TypeEq {
  case class Refl[T]() extends TypeEq[T, T]

  def refl[T]: TypeEq[T, T] =
    Refl()

  def unapply[A, B](ev: A =:= B): Some[TypeEq[A, B]] =
    Some(ev.substituteCo(refl[A]))

  extension [A, B](ev: A =:= B)
    def inFst[Q, F[_, _]]: F[A, Q] =:= F[B, Q] =
      ev.liftCo[F[_, Q]]
    def inSnd[P, F[_, _]]: F[P, A] =:= F[P, B] =
      ev.liftCo[F[P, _]]
    def zip[P, Q, F[_, _]](that: P =:= Q): F[A, P] =:= F[B, Q] =
      that.substituteCo[[x] =>> F[A, P] =:= F[B, x]](ev.inFst[P, F])
}

sealed trait TypeEqK[F[_], G[_]]:
  import TypeEqK.Refl

  def at[X]: F[X] =:= G[X] =
    this match { case Refl() => summon[F[X] =:= G[X]] }

object TypeEqK {
  case class Refl[F[_]]() extends TypeEqK[F, F]

  given refl[F[_]]: TypeEqK[F, F] =
    Refl()

  def ext[F[_], G[_]](f: [x] => Unit => F[x] =:= G[x]): TypeEqK[F[_], G[_]] =
    refl[F].asInstanceOf[TypeEqK[F, G]]
}
