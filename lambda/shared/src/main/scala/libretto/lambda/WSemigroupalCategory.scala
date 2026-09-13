package libretto.lambda

import libretto.lambda.util.Exists

/** A semigroupal category on all Scala types, where the monoidal product (tensor)
  * is not given as a fixed binary type constructor, but is *witnessed* (hence "W" in WSemigroupal)
  * by a ternary relation `Prd[A, B, P]` that `P` is the tensor of `A` and `B`.
  *
  * A non-narrow (i.e. all Scala types are objects) extension of [[NarrowWSemigroupalCategory]],
  * specializing the object witness type to `Unit`.
  *
  * @tparam ->   morphism of the category
  * @tparam Prd  witnesses tensor formation: `Prd[A, B, P]` means that `P` is the tensor of `A` and `B`.
  */
trait WSemigroupalCategory[->[_, _], Prd[_, _, _]]
  extends NarrowWSemigroupalCategory[[x] =>> Unit, ->, Prd]
  with Category[->]
{
  import NarrowWSemigroupalCategory.*

  /** Witnesses that `P` is the tensor of `A` and `B`. */
  def wtensor[A, B]: Exists[[P] =>> Prd[A, B, P]]

  /** Since every Scala type is an object of the category, any type `A`
    * can be viewed as a unary product.
    */
  given [A]: PrdN.Intension[\[A]] =
    PrdN.Intension.atom[A](using ())

  override def wtensor[A, B](wa: Unit, wb: Unit): Exists[[P] =>> Prd[A, B, P]] =
    wtensor[A, B]

  override def tensorObj[A, B, P](p: Prd[A, B, P])(using a: Unit, b: Unit): Unit =
    ()
}