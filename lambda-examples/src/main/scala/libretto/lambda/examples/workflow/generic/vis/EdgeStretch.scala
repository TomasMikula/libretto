package libretto.lambda.examples.workflow.generic.vis

/** A continuous stretch of an edge (input/output),
 * possibly spanning multiple adjacent [[EdgeSegment]]s.
 */
sealed trait EdgeStretch[X] {
  def inl[∙[_, _], R]: EdgeStretch[X ∙ R]
  def inr[∙[_, _], L]: EdgeStretch[L ∙ X]
}

object EdgeStretch {
  case class SinglePoint[X](p: PointOf[X]) extends EdgeStretch[X] {
    override def inl[∙[_, _], R]: EdgeStretch[X ∙ R] = SinglePoint(p.inl)
    override def inr[∙[_, _], L]: EdgeStretch[L ∙ X] = SinglePoint(p.inr)
  }

  case class Line[X, Y](
    leastCover: EdgeSegment[X, Y],
    demarcation: Demarcation[X],
  ) extends EdgeStretch[Y] {
    override def inl[∙[_, _], R]: EdgeStretch[Y ∙ R] = Line(leastCover.inl, demarcation)
    override def inr[∙[_, _], L]: EdgeStretch[L ∙ Y] = Line(leastCover.inr, demarcation)
  }

  sealed trait Demarcation[X]
  object Demarcation {
    case class Whole[X]() extends Demarcation[X]
    case class Leading[∙[_, _], X1, X2](to: InnerPointOf[X2]) extends Demarcation[X1 ∙ X2]
    case class Trailing[∙[_, _], X1, X2](from: InnerPointOf[X1]) extends Demarcation[X1 ∙ X2]
    case class Inner[∙[_, _], X1, X2](from: InnerPointOf[X1], to: InnerPointOf[X2]) extends Demarcation[X1 ∙ X2]
    sealed trait SubWire extends Demarcation[Wire]
    object SubWire {
      case object Pre              extends SubWire
      case object WireLHalf        extends SubWire
      case object WireRHalf        extends SubWire
      case object Post             extends SubWire
      case object LHalf            extends SubWire
      case object RHalf            extends SubWire
      case object WireOnly         extends SubWire
      case object WireAndPre       extends SubWire
      case object WireAndPost      extends SubWire
      case object PaddingMidpoints extends SubWire
      case class Fraction(from: Int, to: Int, total: Int) extends SubWire {
        require(0 <= from)
        require(from <= to)
        require(to <= total)
        require(0 < total)
      }
    }
  }

  sealed trait PointOf[X] {
    def inl[∙[_, _], R]: PointOf[X ∙ R]
    def inr[∙[_, _], L]: PointOf[L ∙ X]
  }

  case class StartOf[X]() extends PointOf[X] {
    override def inl[∙[_, _], R]: PointOf[X ∙ R] = StartOf[X ∙ R]()
    override def inr[∙[_, _], L]: PointOf[L ∙ X] = InnerPointOf.Between(EdgeSegment.Id[L ∙ X]())
  }

  case class EndOf[X]() extends PointOf[X] {
    override def inl[∙[_, _], R]: PointOf[X ∙ R] = InnerPointOf.Between(EdgeSegment.Id[X ∙ R]())
    override def inr[∙[_, _], L]: PointOf[L ∙ X] = EndOf[L ∙ X]()
  }

  sealed trait InnerPointOf[X] extends PointOf[X] {
    override def inl[∙[_, _], R]: InnerPointOf[X ∙ R]
    override def inr[∙[_, _], L]: InnerPointOf[L ∙ X]
  }
  object InnerPointOf {
    case class Between[∙[_, _], X1, X2, Y](seg: EdgeSegment[X1 ∙ X2, Y]) extends InnerPointOf[Y] {
      override def inl[∙[_, _], R]: InnerPointOf[Y ∙ R] = Between(seg.inl)
      override def inr[∙[_, _], L]: InnerPointOf[L ∙ Y] = Between(seg.inr)
    }

    case class SubWire[X](seg: EdgeSegment[Wire, X], p: SubWirePoint) extends InnerPointOf[X] {
      override def inl[∙[_, _], R]: InnerPointOf[X ∙ R] = SubWire(seg.inl, p)
      override def inr[∙[_, _], L]: InnerPointOf[L ∙ X] = SubWire(seg.inr, p)
    }

    enum SubWirePoint:
      case LPadMid
      case WireBegin
      case WireMid
      case WireEnd
      case RPadMid
  }

  import InnerPointOf.*

  def whole[X]: EdgeStretch[X] =
    segment(EdgeSegment.Id())

  def pickL[∙[_, _], L, R]: EdgeStretch[L ∙ R] =
    whole[L].inl

  def pickR[∙[_, _], L, R]: EdgeStretch[L ∙ R] =
    whole[R].inr

  def segment[X, Y](seg: EdgeSegment[X, Y]): EdgeStretch[Y] =
    EdgeStretch.Line(seg, Demarcation.Whole())

  def wireSegment: EdgeStretch[Wire] =
    EdgeStretch.segment(EdgeSegment.pickId[Wire])

  def wireOnly[X](seg: EdgeSegment[Wire, X]): EdgeStretch[X] =
    EdgeStretch.Line(seg, Demarcation.SubWire.WireOnly)

  def wireOnly: EdgeStretch[Wire] =
    wireOnly(EdgeSegment.pickId)

  def wireMidPoint[X](seg: EdgeSegment[Wire, X]): EdgeStretch[X] =
    SinglePoint(InnerPointOf.SubWire(seg, SubWirePoint.WireMid))

  def wireMidPoint: EdgeStretch[Wire] =
    wireMidPoint(EdgeSegment.pickId)

  def wireLHalf[X](seg: EdgeSegment[Wire, X]): EdgeStretch[X] =
    EdgeStretch.Line(seg, Demarcation.SubWire.WireLHalf)

  def wireLHalf: EdgeStretch[Wire] =
    wireLHalf(EdgeSegment.pickId)

  def wireRHalf[X](seg: EdgeSegment[Wire, X]): EdgeStretch[X] =
    EdgeStretch.Line(seg, Demarcation.SubWire.WireRHalf)

  def wireRHalf: EdgeStretch[Wire] =
    wireRHalf(EdgeSegment.pickId)

  def wireFraction[X](from: Int, to: Int, total: Int, seg: EdgeSegment[Wire, X]): EdgeStretch[X] =
    EdgeStretch.Line(seg, Demarcation.SubWire.Fraction(from, to, total))

  def wireFraction(from: Int, to: Int, total: Int): EdgeStretch[Wire] =
    wireFraction(from, to, total, EdgeSegment.pickId)

  def wirePart[X](i: Int, n: Int, seg: EdgeSegment[Wire, X]): EdgeStretch[X] =
    require(i < n)
    wireFraction(i, i+1, n, seg)

  def wirePart(i: Int, n: Int): EdgeStretch[Wire] =
    wirePart(i, n, EdgeSegment.pickId)

  def wireSegLHalf[X](seg: EdgeSegment[Wire, X]): EdgeStretch[X] =
    EdgeStretch.Line(seg, Demarcation.SubWire.LHalf)

  def wireSegLHalf: EdgeStretch[Wire] =
    wireSegLHalf(EdgeSegment.pickId)

  def wireSegRHalf[X](seg: EdgeSegment[Wire, X]): EdgeStretch[X] =
    EdgeStretch.Line(seg, Demarcation.SubWire.RHalf)

  def wireSegRHalf: EdgeStretch[Wire] =
    wireSegRHalf(EdgeSegment.pickId)

  def preWire[X](seg: EdgeSegment[Wire, X]): EdgeStretch[X] =
    EdgeStretch.Line(seg, Demarcation.SubWire.Pre)

  def preWire: EdgeStretch[Wire] =
    preWire(EdgeSegment.pickId)

  def postWire[X](seg: EdgeSegment[Wire, X]): EdgeStretch[X] =
    EdgeStretch.Line(seg, Demarcation.SubWire.Post)

  def postWire: EdgeStretch[Wire] =
    postWire(EdgeSegment.pickId)

  def wireAndPre[X](seg: EdgeSegment[Wire, X]): EdgeStretch[X] =
    EdgeStretch.Line(seg, Demarcation.SubWire.WireAndPre)

  def wireAndPre: EdgeStretch[Wire] =
    wireAndPre(EdgeSegment.pickId)

  def wireAndPost[X](seg: EdgeSegment[Wire, X]): EdgeStretch[X] =
    EdgeStretch.Line(seg, Demarcation.SubWire.WireAndPost)

  def wireAndPost: EdgeStretch[Wire] =
    wireAndPost(EdgeSegment.pickId)

  def paddingMidpoints[X](seg: EdgeSegment[Wire, X]): EdgeStretch[X] =
    EdgeStretch.Line(seg, Demarcation.SubWire.PaddingMidpoints)

  def paddingMidpoints: EdgeStretch[Wire] =
    paddingMidpoints(EdgeSegment.pickId)

  /** Tightest stretch containing all wires. */
  def trimPadding[X](x: EdgeDesc[X]): EdgeStretch[X] =
    x match
      case EdgeDesc.SingleWire =>
        EdgeStretch.wireOnly
      case x: EdgeDesc.Binary[op, x1, x2] =>
        EdgeStretch.Line(
          EdgeSegment.pickId,
          EdgeStretch.Demarcation.Inner[op, x1, x2](
            wiresStartPoint(x.x1),
            wiresEndPoint(x.x2),
          ),
        )

  private def wiresStartPoint[X](x: EdgeDesc[X]): EdgeStretch.InnerPointOf[X] =
    x match
      case EdgeDesc.SingleWire => EdgeStretch.InnerPointOf.SubWire(EdgeSegment.pickId, SubWirePoint.WireBegin)
      case x: EdgeDesc.Binary[op, x1, x2] => wiresStartPoint(x.x1).inl[op, x2]

  private def wiresEndPoint[X](x: EdgeDesc[X]): EdgeStretch.InnerPointOf[X] =
    import EdgeStretch.InnerPointOf.SubWirePoint.WireEnd
    x match
      case EdgeDesc.SingleWire => EdgeStretch.InnerPointOf.SubWire(EdgeSegment.pickId, WireEnd)
      case x: EdgeDesc.Binary[op, x1, x2] => wiresEndPoint(x.x2).inr[op, x1]

  def paddingMidpoints[X](x: EdgeDesc[X]): EdgeStretch[X] =
    x match
      case EdgeDesc.SingleWire =>
        EdgeStretch.paddingMidpoints
      case x: EdgeDesc.Binary[op, x1, x2] =>
        EdgeStretch.Line(
          EdgeSegment.pickId,
          EdgeStretch.Demarcation.Inner[op, x1, x2](
            lPadMidpoint(x.x1),
            rPadMidpoint(x.x2),
          ),
        )

  private def lPadMidpoint[X](x: EdgeDesc[X]): EdgeStretch.InnerPointOf[X] =
    x match
      case EdgeDesc.SingleWire => EdgeStretch.InnerPointOf.SubWire(EdgeSegment.pickId, SubWirePoint.LPadMid)
      case x: EdgeDesc.Binary[op, x1, x2] => lPadMidpoint(x.x1).inl[op, x2]

  private def rPadMidpoint[X](x: EdgeDesc[X]): EdgeStretch.InnerPointOf[X] =
    x match
      case EdgeDesc.SingleWire => EdgeStretch.InnerPointOf.SubWire(EdgeSegment.pickId, SubWirePoint.RPadMid)
      case x: EdgeDesc.Binary[op, x1, x2] => rPadMidpoint(x.x2).inr[op, x1]
}
