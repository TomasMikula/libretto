package libretto.lambda.examples.workflow.generic.lang

import libretto.lambda.{CocartesianSemigroupalCategory, Distribution, Shuffled, SymmetricSemigroupalCategory}
import libretto.lambda.util.Masked

import scala.concurrent.duration.FiniteDuration

sealed trait FlowAST[Op[_, _], A, B] {
  import FlowAST.*

  def >>>[C](that: FlowAST[Op, B, C]): FlowAST[Op, A, C] =
    FlowAST.AndThen(this, that)

  def maskInput: Masked[[a] =>> FlowAST[Op, a, B], A] =
    Masked(this)

  def to[C](using ev: B =:= C): FlowAST[Op, A, C] =
    ev.substituteCo(this)

  def translate[F[_, _]](h: [x, y] => Op[x, y] => F[x, y]): FlowAST[F, A, B] =
    this match {
      case Ext(action)                  => Ext(h(action))
      case AndThen(f, g)                => AndThen(f.translate(h), g.translate(h))
      case Par(f1, f2)                  => Par(f1.translate(h), f2.translate(h))
      case Either(f, g)                 => Either(f.translate(h), g.translate(h))
      case DoWhile(f)                   => DoWhile(f.translate(h))
      case Id()                         => Id()
      case _: Swap[op, x, y]            => Swap[F, x, y]()
      case _: AssocLR[op, x, y, z]      => AssocLR[F, x, y, z]()
      case _: AssocRL[op, x, y, z]      => AssocRL[F, x, y, z]()
      case _: InjectL[op, x, y]         => InjectL[F, x, y]()
      case _: InjectR[op, x, y]         => InjectR[F, x, y]()
      case _: Prj1[op, x, y]            => Prj1[F, x, y]()
      case _: Prj2[op, x, y]            => Prj2[F, x, y]()
      case Dup()                        => Dup()
      case IntroFst()                   => IntroFst()
      case _: DistributeLR[op, x, y, z] => DistributeLR[F, x, y , z]()
      case _: Read[op, x]               => Read[F, x]()
      case _: ReadAwait[op, x]          => ReadAwait[F, x]()
      case r: ReadAwaitTimeout[op, x]   => ReadAwaitTimeout[F, x](r.duration)
      case Delay(duration)              => Delay(duration)
    }

  def toShuffled(using shuffled: Shuffled[FlowAST.Work[Op, _, _], **]): shuffled.Shuffled[A, B] =
    this match
      case Id()                    => shuffled.id
      case AndThen(f, g)           => f.toShuffled > g.toShuffled
      case _: AssocLR[op, x, y, z] => shuffled.assocLR[x, y, z]
      case _: AssocRL[op, x, y, z] => shuffled.assocRL[x, y, z]
      case Par(f1, f2)             => shuffled.par(f1.toShuffled, f2.toShuffled)
      case _: Swap[op, x, y]       => shuffled.swap[x, y]
      case f: Work[Op, A, B]       => shuffled.lift(f)

}

object FlowAST {
  case class Id[Op[_, _], A]() extends FlowAST[Op, A, A]
  case class AndThen[Op[_, _], A, B, C](f: FlowAST[Op, A, B], g: FlowAST[Op, B, C]) extends FlowAST[Op, A, C]
  case class AssocLR[Op[_, _], A, B, C]() extends FlowAST[Op, (A ** B) ** C, A ** (B ** C)]
  case class AssocRL[Op[_, _], A, B, C]() extends FlowAST[Op, A ** (B ** C), (A ** B) ** C]
  case class Par[Op[_, _], A1, A2, B1, B2](f1: FlowAST[Op, A1, B1], f2: FlowAST[Op, A2, B2]) extends FlowAST[Op, A1 ** A2, B1 ** B2]
  case class Swap[Op[_, _], A, B]() extends FlowAST[Op, A ** B, B ** A]

  sealed trait Work[Op[_, _], A, B] extends FlowAST[Op, A, B] {
    override def maskInput: Masked[[a] =>> Work[Op, a, B], A] =
      Masked(this)
  }
  case class IntroFst[Op[_, _], A]() extends Work[Op, A, Unit ** A]
  case class Prj1[Op[_, _], A, B]() extends Work[Op, A ** B, A]
  case class Prj2[Op[_, _], A, B]() extends Work[Op, A ** B, B]
  case class Dup[Op[_, _], A]() extends Work[Op, A, A ** A]
  case class InjectL[Op[_, _], A, B]() extends Work[Op, A, A ++ B]
  case class InjectR[Op[_, _], A, B]() extends Work[Op, B, A ++ B]
  case class Either[Op[_, _], A, B, C](f: FlowAST[Op, A, C], g: FlowAST[Op, B, C]) extends Work[Op, A ++ B, C]
  case class DistributeLR[Op[_, _], A, B, C]() extends Work[Op, A ** (B ++ C), (A ** B) ++ (A ** C)]
  case class DoWhile[Op[_, _], A, B](f: FlowAST[Op, A, A ++ B]) extends Work[Op, A, B]
  case class Delay[Op[_, _], A](duration: FiniteDuration) extends Work[Op, A, A]

  case class Read[Op[_, _], A]() extends Work[Op, Unit, PortName[A] ** Reading[A]]
  case class ReadAwait[Op[_, _], A]() extends Work[Op, Reading[A], A]
  case class ReadAwaitTimeout[Op[_, _], A](duration: FiniteDuration) extends Work[Op, Reading[A], A ++ Reading[A]]

  /** Extension point for pluggable actions. */
  case class Ext[Op[_, _], A, B](action: Op[A, B]) extends Work[Op, A, B]

  given ssc[Op[_, _]]: SymmetricSemigroupalCategory[FlowAST[Op, _, _], **] with {
    override def id[A]: FlowAST[Op, A, A] = Id()
    override def andThen[A, B, C](f: FlowAST[Op, A, B], g: FlowAST[Op, B, C]): FlowAST[Op, A, C] = AndThen(f, g)
    override def assocLR[A, B, C]: FlowAST[Op, (A ** B) ** C, A ** (B ** C)] = AssocLR()
    override def assocRL[A, B, C]: FlowAST[Op, A ** (B ** C), (A ** B) ** C] = AssocRL()
    override def par[A1, A2, B1, B2](f1: FlowAST[Op, A1, B1], f2: FlowAST[Op, A2, B2]): FlowAST[Op, A1 ** A2, B1 ** B2] = Par(f1, f2)
    override def swap[A, B]: FlowAST[Op, A ** B, B ** A] = Swap()
  }

  given cocat[Op[_, _]]: CocartesianSemigroupalCategory[FlowAST[Op, _, _], ++] with {
    override def andThen[A, B, C](f: FlowAST[Op, A, B], g: FlowAST[Op, B, C]): FlowAST[Op, A, C] = AndThen(f, g)
    override def id[A]: FlowAST[Op, A, A] = Id()
    override def injectL[A, B]: FlowAST[Op, A, A ++ B] = InjectL()
    override def injectR[A, B]: FlowAST[Op, B, A ++ B] = InjectR()
    override def either[A, B, C](f: FlowAST[Op, A, C], g: FlowAST[Op, B, C]): FlowAST[Op, A ++ B, C] = Either(f, g)
  }

  given distr[Op[_, _]]: Distribution[FlowAST[Op, _, _], **, ++] with {
    override val cat: SymmetricSemigroupalCategory[FlowAST[Op, _, _], **] = ssc[Op]
    import cat.*
    override def distLR[A, B, C]: FlowAST[Op, A ** (B ++ C), A ** B ++ A ** C] = DistributeLR()
    override def distRL[A, B, C]: FlowAST[Op, (A ++ B) ** C, A ** C ++ B ** C] = swap[A ++ B, C] > distLR > cocat[Op].par(Swap(), Swap())
  }

  def shuffled[Op[_, _]]: Shuffled[Work[Op, _, _], **] =
    Shuffled[Work[Op, _, _], **]

  def fromShuffled[Op[_, _], A, B](using
    shuffled: Shuffled[FlowAST.Work[Op, _, _], **],
  )(
    f: shuffled.Shuffled[A, B],
  ): FlowAST[Op[_, _], A, B] =
    f.foldMap[FlowAST[Op, _, _]]([x, y] => (w: Work[Op, x, y]) => w)
}
