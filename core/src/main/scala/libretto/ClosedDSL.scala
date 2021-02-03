package libretto

/** Extension of [[CoreDSL]] that adds support for "functions as data" (`=⚬`).
  * In other words, it makes [[CoreDSL.-⚬]] a ''closed'' monoidal category.
  */
trait ClosedDSL extends CoreDSL {
  /** Linear function as data, that is, one that can be part of an input or output of a linear function (`-⚬`).
    * While `A -⚬ B` is a morphism in a category, `A =⚬ B` is an object called the internal hom of `A` and `B`
    * in a closed monoidal category.
    */
  type =⚬[A, B]

  def curry[A, B, C](f: (A |*| B) -⚬ C): A -⚬ (B =⚬ C)

  def eval[A, B]: ((A =⚬ B) |*| A) -⚬ B

  def uncurry[A, B, C](f: A -⚬ (B =⚬ C)): (A |*| B) -⚬ C =
    andThen(par(f, id[B]), eval[B, C])
}
