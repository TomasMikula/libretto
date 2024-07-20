package libretto.cats

import libretto.lambda.SemigroupalCategory
import libretto.util.Equal

trait Cosemigroup[->[_, _], **[_, _], A] {
  def cat: SemigroupalCategory[->, **]

  def split: A -> (A ** A)

  def law_coAssociativity: Equal[ A -> ((A ** A) ** A) ] =
    val c = cat
    import c.*

    Equal(
      andThen(split, par(split, id[A])),
      andThen(andThen(split, par(id[A], split)), assocRL),
    )
}
