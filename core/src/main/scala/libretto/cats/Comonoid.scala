package libretto.cats

import libretto.lambda.MonoidalCategory
import libretto.util.Equal

/** Witnesses that `A` is a comonoid object
 *  in the monoidal category `->` with monoidal product `**` and unit object `One`.
 */
trait Comonoid[->[_, _], **[_, _], One, A] extends Cosemigroup[->, **, A] with Affine[->, One, A] {
  override def cat: MonoidalCategory[->, **, One]

  def counit: A -> One

  override def discard: A -> One =
    counit

  def law_leftCounit: Equal[ A -> (One ** A) ] =
    val c = cat
    import c.*

    Equal(
      andThen(this.split, par(counit, id[A])),
      introFst,
    )

  def law_rightCounit: Equal[ A -> (A ** One) ] =
    val c = cat
    import c.*

    Equal(
      andThen(this.split, par(id[A], counit)),
      introSnd,
    )
}
