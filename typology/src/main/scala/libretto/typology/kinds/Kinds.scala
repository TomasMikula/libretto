package libretto.typology.kinds

/** Evidence that `K` represents zero or more kinds. */
sealed trait Kinds[K] {
  def nonEmpty: Either[K =:= ○, KindN[K]]

  override def toString: String =
    this match
      case Kinds.Empty       => "○"
      case Kinds.NonEmpty(k) => k.toString

  def testEqual[L](that: Kinds[L]): Option[K =:= L] =
    (this, that) match {
      case (Kinds.Empty, Kinds.Empty) =>
        Some(implicitly[○ =:= ○])
      case (Kinds.NonEmpty(k), Kinds.NonEmpty(l)) =>
        k testEqual l
      case _ =>
        None
    }
}

object Kinds {
  case object Empty extends Kinds[○] {
    override def nonEmpty = Left(summon[○ =:= ○])
  }

  case class NonEmpty[K](value: KindN[K]) extends Kinds[K] {
    override def nonEmpty: Either[K =:= ○, KindN[K]] = Right(value)
  }

  def apply[K](using k: Kinds[K]): Kinds[K] =
    k

  def apply[K](k: Kind[K]): Kinds[K] =
    k match {
      case Kind.Type => NonEmpty(KindN.Type)
    }

  def apply[K](k: KindN[K]): Kinds[K] =
    NonEmpty(k)

  given Kinds[○] = Empty
  given [K](using k: KindN[K]): Kinds[K] = Kinds(k)

  def nonEmpty[K, L](kl: Kinds[K × L]): KindN[K × L] =
    kl match
      case NonEmpty(kl) => kl

  def unpair[K, L](kl: Kinds[K × L]): (KindN[K], KindN[L]) =
    kl match
      case NonEmpty(kl) => KindN.unpair(kl)

  def fstOf[K, L](kl: Kinds[K × L]): KindN[K] =
    unpair(kl)._1

  def sndOf[K, L](kl: Kinds[K × L]): KindN[L] =
    unpair(kl)._2

  val unitIsNotPair: [x, y] => (○ =:= (x × y)) => Nothing =
    [x, y] => (ev: ○ =:= (x × y)) => {
      val k: KindN[○] = ev.substituteContra(nonEmpty(ev.substituteCo(summon[Kinds[○]])))
      KindN.cannotBeUnit(k)
    }
}
