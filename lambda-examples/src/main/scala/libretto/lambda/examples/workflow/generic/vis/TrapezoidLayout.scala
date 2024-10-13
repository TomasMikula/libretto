package libretto.lambda.examples.workflow.generic.vis

import DefaultDimensions.Length
import IOLayout.EdgeLayout
import Px.*
import util.IntegralProportions

final case class TrapezoidLayout[I, O](
  iOffset: Px,
  oOffset: Px,
  iLayout: EdgeLayout[I],
  oLayout: EdgeLayout[O],
  height: Px,
) {
  def *(k: Int): TrapezoidLayout[I, O] =
    require(k > 0)
    TrapezoidLayout(
      iOffset * k,
      oOffset * k,
      iLayout * k,
      oLayout * k,
      height  * k,
    )

  def inWireCoords(wire: WirePick[I]): EdgeLayout.WireCoords =
    iLayout.wireCoords(wire).offset(iOffset)

  def outWireCoords(wire: WirePick[O]): EdgeLayout.WireCoords =
    oLayout.wireCoords(wire).offset(oOffset)

  def inSegmentCoords(seg: EdgeStretch[I]): EdgeLayout.SegmentCoords =
    iLayout.coordsOf(seg).offset(iOffset)

  def outSegmentCoords[S](seg: EdgeStretch[O]): EdgeLayout.SegmentCoords =
    oLayout.coordsOf(seg).offset(oOffset)

  def vsplit[X](xLayout: EdgeLayout[X])(
    iLen: Length,
    oLen: Length,
  ): (Int, TrapezoidLayout[I, X], TrapezoidLayout[X, O]) = {
    val IntegralProportions(k, List(ih, oh)) =
      Length.divideProportionally(height.pixels)(iLen, oLen)
    val TrapezoidLayout(iOff, oOff, iLay, oLay, _) = this * k
    val mOff = Px((iOff * ih + oOff * oh).pixels / (ih + oh))
    val mLay = xLayout * k
    ( k
    , TrapezoidLayout(iOff, mOff, iLay, mLay, ih.px)
    , TrapezoidLayout(mOff, oOff, mLay, oLay, oh.px)
    )
  }
}

object TrapezoidLayout {
  def apply[I, O](
    iLayout: EdgeLayout[I],
    oLayout: EdgeLayout[O],
    height: Px,
  ): TrapezoidLayout[I, O] =
    TrapezoidLayout(0.px, 0.px, iLayout, oLayout, height)

  def apply[I, O](
    ioLayout: IOLayout[I, O],
    height: Px,
  ): TrapezoidLayout[I, O] =
    TrapezoidLayout(ioLayout.inEdge, ioLayout.outEdge, height)

  def split[∙[_, _], I1, I2, O1, O2](
    reg: TrapezoidLayout[I1 ∙ I2, O1 ∙ O2],
  ): (
    TrapezoidLayout[I1, O1],
    TrapezoidLayout[I2, O2],
  ) = {
    val TrapezoidLayout(iOff, oOff, iLayout, oLayout, height) = reg
    val (i1, i2) = EdgeLayout.split(iLayout)
    val (o1, o2) = EdgeLayout.split(oLayout)
    (
      TrapezoidLayout(iOff, oOff, i1, o1, height),
      TrapezoidLayout(iOff + i1.pixelBreadth, oOff + o1.pixelBreadth, i2, o2, height)
    )
  }
}
