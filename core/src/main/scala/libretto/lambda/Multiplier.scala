package libretto.lambda

sealed trait Multiplier[|*|[_, _], A, A1] {
  def compile[->[_, _]](split: A -> (A |*| A))(using
    c: SemigroupalCategory[->, |*|],
  ): A -> A1 =
    this match {
      case Multiplier.Id() => c.id[A]
      case Multiplier.Dup(f, g) => split > c.par(f.compile(split), g.compile(split))
    }
}

object Multiplier {
  case class Id[|*|[_, _], A]() extends Multiplier[|*|, A, A]
  case class Dup[|*|[_, _], A, A1, A2](
    f: Multiplier[|*|, A, A1],
    g: Multiplier[|*|, A, A2],
  ) extends Multiplier[|*|, A, A1 |*| A2]

  def id[|*|[_, _], A]: Multiplier[|*|, A, A] =
    Id()

  def dup[|*|[_, _], A, A1, A2](
    f: Multiplier[|*|, A, A1],
    g: Multiplier[|*|, A, A2],
  ): Multiplier[|*|, A, A1 |*| A2] =
    Dup(f, g)

  def dup[|*|[_, _], A]: Multiplier[|*|, A, A |*| A] =
    dup(id, id)
}
