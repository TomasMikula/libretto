package libretto.lambda.examples.workflow.generic.lang

import libretto.lambda.SymmetricSemigroupalCategory

sealed trait FlowAST[Op[_, _], A, B] {
  import FlowAST.*

  def >>>[C](that: FlowAST[Op, B, C]): FlowAST[Op, A, C] =
    FlowAST.AndThen(this, that)

  def translate[F[_, _]](f: [x, y] => Op[x, y] => F[x, y]): FlowAST[F, A, B] =
    this match {
      case DomainAction(action) => DomainAction(f(action))
      case other                => other.asInstanceOf[FlowAST[F, A, B]]
    }
}

object FlowAST {
  case class Id[Op[_, _], A]() extends FlowAST[Op, A, A]
  case class AndThen[Op[_, _], A, B, C](f: FlowAST[Op, A, B], g: FlowAST[Op, B, C]) extends FlowAST[Op, A, C]
  case class AssocLR[Op[_, _], A, B, C]() extends FlowAST[Op, (A ** B) ** C, A ** (B ** C)]
  case class AssocRL[Op[_, _], A, B, C]() extends FlowAST[Op, A ** (B ** C), (A ** B) ** C]
  case class Par[Op[_, _], A1, A2, B1, B2](f1: FlowAST[Op, A1, B1], f2: FlowAST[Op, A2, B2]) extends FlowAST[Op, A1 ** A2, B1 ** B2]
  case class Swap[Op[_, _], A, B]() extends FlowAST[Op, A ** B, B ** A]
  case class IntroFst[Op[_, _], A]() extends FlowAST[Op, A, Unit ** A]
  case class Prj1[Op[_, _], A, B]() extends FlowAST[Op, A ** B, A]
  case class Prj2[Op[_, _], A, B]() extends FlowAST[Op, A ** B, B]
  case class Dup[Op[_, _], A]() extends FlowAST[Op, A, A ** A]
  case class Either[Op[_, _], A, B, C](f: FlowAST[Op, A, C], g: FlowAST[Op, B, C]) extends FlowAST[Op, A ++ B, C]
  case class DistributeLR[Op[_, _], A, B, C]() extends FlowAST[Op, A ** (B ++ C), (A ** B) ++ (A ** C)]

  case class Promise[Op[_, _], A]() extends FlowAST[Op, Unit, PromiseRef[A] ** A]

  case class DomainAction[Op[_, _], A, B](action: Op[A, B]) extends FlowAST[Op, A, B]

  given ssc[Op[_, _]]: SymmetricSemigroupalCategory[FlowAST[Op, _, _], **] with {
    override def id[A]: FlowAST[Op, A, A] = Id()
    override def andThen[A, B, C](f: FlowAST[Op, A, B], g: FlowAST[Op, B, C]): FlowAST[Op, A, C] = AndThen(f, g)
    override def assocLR[A, B, C]: FlowAST[Op, (A ** B) ** C, A ** (B ** C)] = AssocLR()
    override def assocRL[A, B, C]: FlowAST[Op, A ** (B ** C), (A ** B) ** C] = AssocRL()
    override def par[A1, A2, B1, B2](f1: FlowAST[Op, A1, B1], f2: FlowAST[Op, A2, B2]): FlowAST[Op, A1 ** A2, B1 ** B2] = Par(f1, f2)
    override def swap[A, B]: FlowAST[Op, A ** B, B ** A] = Swap()
  }
}
