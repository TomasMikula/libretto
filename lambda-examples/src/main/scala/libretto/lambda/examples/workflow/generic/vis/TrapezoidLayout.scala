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

  def outSegmentCoords(seg: EdgeStretch[O]): EdgeLayout.SegmentCoords =
    oLayout.coordsOf(seg).offset(oOffset)

  def subSegment[X, Y](
    iSeg: EdgeSegment[X, I],
    oSeg: EdgeSegment[Y, O],
  ): TrapezoidLayout[X, Y] = {
    val (ix, iLay) = iLayout.locate(iSeg)
    val (ox, oLay) = oLayout.locate(oSeg)
    TrapezoidLayout(iOffset + ix, oOffset + ox, iLay, oLay, height)
  }

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

  def singleOut[I, Wrap[_], O](
    reg: TrapezoidLayout[I, Wrap[Only[O]]],
  ): TrapezoidLayout[I, O] =
    val TrapezoidLayout(iOff, oOff, iLayout, oLayout, height) = reg
    TrapezoidLayout(iOff, oOff, iLayout, EdgeLayout.single(oLayout), height)

  def single[Wrap[_], I, O](
    reg: TrapezoidLayout[Wrap[Only[I]], Wrap[Only[O]]]
  ): TrapezoidLayout[I, O] =
    val TrapezoidLayout(iOff, oOff, iLayout, oLayout, height) = reg
    TrapezoidLayout(iOff, oOff, EdgeLayout.single(iLayout), EdgeLayout.single(oLayout), height)

  def unsnocOut[I, Wrap[_], O1, O2, O3](
    reg: TrapezoidLayout[I, Wrap[((O1, O2), O3)]],
  ): (
    TrapezoidLayout[I, Wrap[(O1, O2)]],
    TrapezoidLayout[I, O3],
  ) =
    val TrapezoidLayout(iOff, oOff, iLayout, oLayout, height) = reg
    val (oLayInit, oLayLast) = EdgeLayout.unsnoc(oLayout)
    (
      TrapezoidLayout(iOff, oOff                        , iLayout, oLayInit, height),
      TrapezoidLayout(iOff, oOff + oLayInit.pixelBreadth, iLayout, oLayLast, height),
    )

  def unsnoc[Wrap[_], I1, I2, I3, O1, O2, O3](
    reg: TrapezoidLayout[Wrap[((I1, I2), I3)], Wrap[((O1, O2), O3)]],
  ): (
    TrapezoidLayout[Wrap[(I1, I2)], Wrap[(O1, O2)]],
    TrapezoidLayout[I3, O3],
  ) =
    val TrapezoidLayout(iOff, oOff, iLayout, oLayout, height) = reg
    val (iLayInit, iLayLast) = EdgeLayout.unsnoc(iLayout)
    val (oLayInit, oLayLast) = EdgeLayout.unsnoc(oLayout)
    (
      TrapezoidLayout(iOff                        , oOff                        , iLayInit, oLayInit, height),
      TrapezoidLayout(iOff + iLayInit.pixelBreadth, oOff + oLayInit.pixelBreadth, iLayLast, oLayLast, height),
    )
}
