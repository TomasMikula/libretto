package libretto.util

/** Type equality that, unlike Scala's `=:=`, can be pattern matched on. */
sealed trait TypeEq[A, B]

object TypeEq {
  case class Refl[T]() extends TypeEq[T, T]

  def refl[T]: TypeEq[T, T] =
    Refl()

  def unapply[A, B](ev: A =:= B): Some[TypeEq[A, B]] =
    Some(ev.substituteCo(refl[A]))
}
