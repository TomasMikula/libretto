package libretto.lambda

/** A semigroupal category on a subset of Scala types.
 *
 * @tparam ->   morphism of the category
 * @tparam |*|  the monoidal product (tensor)
 * @tparam Obj  witnesses that a Scala type is an object of the category.
 */
trait NarrowSemigroupalCategory[->[_, _], |*|[_, _], Obj[_]]
  extends NarrowCategory[->, Obj]
{
  def par[A1, A2, B1, B2](f1: A1 -> B1, f2: A2 -> B2): (A1 |*| A2) -> (B1 |*| B2)

  /** Combines the object-witnesses of two objects into an object-witness for their tensor (monoidal product). */
  def tensor[A, B](wa: Obj[A], wb: Obj[B]): Obj[A |*| B]

  def assocLR[A, B, C](a: Obj[A], b: Obj[B], c: Obj[C]): ((A |*| B) |*| C) -> (A |*| (B |*| C))
  def assocRL[A, B, C](a: Obj[A], b: Obj[B], c: Obj[C]): (A |*| (B |*| C)) -> ((A |*| B) |*| C)

  def fst[X, Y, Z](f: X -> Y)(using z: Obj[Z]): (X |*| Z) -> (Y |*| Z) =
    par(f, id(z))

  def snd[X, Y, Z](f: Y -> Z)(using x: Obj[X]): (X |*| Y) -> (X |*| Z) =
    par(id(x), f)
}
