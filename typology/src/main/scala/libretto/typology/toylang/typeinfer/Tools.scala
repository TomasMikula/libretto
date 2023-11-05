package libretto.typology.toylang.typeinfer

import libretto.scaletto.StarterKit._
import libretto.typology.toylang.terms.TypedFun
import libretto.typology.toylang.types.AbstractTypeLabel

trait Tools { self =>
  type Label

  type OutboundType

  type InboundType

  type OutwardType

  type Type = TypedFun.Type

  trait Nested {
    val tools: Tools
    def unnest: tools.OutboundType -⚬ self.OutboundType
    def unnestOutward: tools.OutwardType -⚬ self.OutwardType
    def mergeLower: (tools.OutwardType |*| tools.OutwardType) -⚬ self.OutwardType
    def mergeZap: (tools.OutwardType |*| tools.OutwardType) -⚬ Val[Type]
  }

  def label(v: AbstractTypeLabel): One -⚬ Label
  def abstractTypeTap: Label -⚬ (OutboundType |*| Val[Type])
  def newAbstractType: Label -⚬ (OutboundType |*| Val[Type] |*| OutboundType)
  def newAbstractTypeGen: Label -⚬ (OutwardType |*| Val[Type] |*| OutwardType)
  def newTypeParam: Label -⚬ (Val[Type] |*| OutwardType)
  def merge: (OutboundType |*| OutboundType) -⚬ OutboundType
  def split: OutboundType -⚬ (OutboundType |*| OutboundType)
  def output: OutboundType -⚬ Val[Type]
  def outputGen: OutwardType -⚬ Val[Type]
  def close: OutboundType -⚬ Done
  def closeGen: OutwardType -⚬ Done
  def debugPrintGradually: OutboundType -⚬ Done
  def pair: (OutboundType |*| OutboundType) -⚬ OutboundType
  def pairOW: (OutwardType |*| OutwardType) -⚬ OutwardType
  def isPair: OutboundType -⚬ (OutboundType |+| (OutboundType |*| OutboundType))
  def recCall: (OutboundType |*| OutboundType) -⚬ OutboundType
  def isRecCall: OutboundType -⚬ (OutboundType |+| (OutboundType |*| OutboundType))

  lazy val nested: Nested
}
