package kindville

/** Type equality for any-kinded types. */
trait =~=[A <: AnyKind, B <: AnyKind] {

  def substituteCo    [F[_ <: AnyKind]](fa: F[A]): F[B]
  def substituteContra[F[_ <: AnyKind]](fa: F[B]): F[A]
}

object =~= {
  case class Refl[A <: AnyKind]() extends =~=[A, A] {
    override def substituteCo    [F[_ <: AnyKind]](fa: F[A]): F[A] = fa
    override def substituteContra[F[_ <: AnyKind]](fa: F[A]): F[A] = fa
  }

  given [A <: AnyKind] => =~=[A, A] =
    Refl()
}
