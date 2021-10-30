package libretto

trait InvertDSL extends ClosedDSL {
  type -[A]

  def backvert[A]: (A |*| -[A]) -⚬ One
  def forevert[A]: One -⚬ (-[A] |*| A)

  def distributeInversion[A, B]: -[A |*| B] -⚬ (-[A] |*| -[B])
  def factorOutInversion[A, B]: (-[A] |*| -[B]) -⚬ -[A |*| B]

  private val coreLib = CoreLib(this)
  import coreLib._

  override type =⚬[A, B] = -[A] |*| B

  override def eval[A, B]: ((A =⚬ B) |*| A) -⚬ B =
    swap > assocRL > elimFst(backvert)

  override def curry[A, B, C](f: (A |*| B) -⚬ C): A -⚬ (B =⚬ C) =
    introFst(forevert[B]) > assocLR > snd(swap > f)

  override def out[A, B, C](f: B -⚬ C): (A =⚬ B) -⚬ (A =⚬ C) =
    snd(f)

  /** Double-inversion elimination. */
  def die[A]: -[-[A]] -⚬ A =
    introSnd(forevert[A]) > assocRL > elimFst(swap > backvert[-[A]])

  /** Double-inversion introduction. */
  def dii[A]: A -⚬ -[-[A]] =
    introFst(forevert[-[A]]) > assocLR > elimSnd(swap > backvert[A])

  def contrapositive[A, B](f: A -⚬ B): -[B] -⚬ -[A] =
    introFst(forevert[A] > snd(f)) > assocLR > elimSnd(backvert[B])

  def unContrapositive[A, B](f: -[A] -⚬ -[B]): B -⚬ A =
    dii[B] > contrapositive(f) > die[A]

  def distributeInversionInto_|+|[A, B]: -[A |+| B] -⚬ (-[A] |&| -[B]) =
    choice(
      contrapositive(injectL[A, B]),
      contrapositive(injectR[A, B]),
    )

  def factorInversionOutOf_|+|[A, B]: (-[A] |+| -[B]) -⚬ -[A |&| B] =
    either(
      contrapositive(chooseL[A, B]),
      contrapositive(chooseR[A, B]),
    )

  def distributeInversionInto_|&|[A, B]: -[A |&| B] -⚬ (-[A] |+| -[B]) =
    unContrapositive(distributeInversionInto_|+| > |&|.bimap(die, die) > dii)

  def factorInversionOutOf_|&|[A, B]: (-[A] |&| -[B]) -⚬ -[A |+| B] =
    unContrapositive(die > |+|.bimap(dii, dii) > factorInversionOutOf_|+|)

  def invertClosure[A, B]: -[A =⚬ B] -⚬ (B =⚬ A) =
    distributeInversion > swap > snd(die)

  def unInvertClosure[A, B]: (A =⚬ B) -⚬ -[B =⚬ A] =
    snd(dii) > swap > factorOutInversion
}
