package libretto.lambda.examples.workflow.generic.lang

import libretto.lambda.{Shuffled, SymmetricSemigroupalCategory}

import scala.concurrent.duration.FiniteDuration

sealed trait FlowAST[Op[_, _], A, B] {
  import FlowAST.*

  def >>>[C](that: FlowAST[Op, B, C]): FlowAST[Op, A, C] =
    FlowAST.AndThen(this, that)

  def translate[F[_, _]](h: [x, y] => Op[x, y] => F[x, y]): FlowAST[F, A, B] =
    this match {
      case DomainAction(action) => DomainAction(h(action))
      case AndThen(f, g)        => AndThen(f.translate(h), g.translate(h))
      case Par(f1, f2)          => Par(f1.translate(h), f2.translate(h))
      case Either(f, g)         => Either(f.translate(h), g.translate(h))
      case other                => other.asInstanceOf[FlowAST[F, A, B]]
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

  sealed trait Work[Op[_, _], A, B] extends FlowAST[Op, A, B]
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

  case class Promise[Op[_, _], A]() extends Work[Op, Unit, PromiseRef[A] ** A]
  case class IsComplete[Op[_, _], A]() extends Work[Op, PromiseRef[A], Unit ++ Unit]

  case class DomainAction[Op[_, _], A, B](action: Op[A, B]) extends Work[Op, A, B]

  given ssc[Op[_, _]]: SymmetricSemigroupalCategory[FlowAST[Op, _, _], **] with {
    override def id[A]: FlowAST[Op, A, A] = Id()
    override def andThen[A, B, C](f: FlowAST[Op, A, B], g: FlowAST[Op, B, C]): FlowAST[Op, A, C] = AndThen(f, g)
    override def assocLR[A, B, C]: FlowAST[Op, (A ** B) ** C, A ** (B ** C)] = AssocLR()
    override def assocRL[A, B, C]: FlowAST[Op, A ** (B ** C), (A ** B) ** C] = AssocRL()
    override def par[A1, A2, B1, B2](f1: FlowAST[Op, A1, B1], f2: FlowAST[Op, A2, B2]): FlowAST[Op, A1 ** A2, B1 ** B2] = Par(f1, f2)
    override def swap[A, B]: FlowAST[Op, A ** B, B ** A] = Swap()
  }

  def shuffled[Op[_, _]]: Shuffled[Work[Op, _, _], **] =
    Shuffled[Work[Op, _, _], **]
}
