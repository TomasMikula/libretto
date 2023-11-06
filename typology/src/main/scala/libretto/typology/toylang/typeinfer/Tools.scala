package libretto.typology.toylang.typeinfer

import libretto.scaletto.StarterKit._
import libretto.typology.toylang.terms.TypedFun
import libretto.typology.toylang.types.{AbstractTypeLabel, TypeTag}

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

  /*
   * Language-specific operations.
   *
   * TODO: abstract away
   */

  def debugPrintGradually: OutboundType -⚬ Done
  def pair: (OutboundType |*| OutboundType) -⚬ OutboundType
  def pairOW: (OutwardType |*| OutwardType) -⚬ OutwardType
  def isPair: OutboundType -⚬ (OutboundType |+| (OutboundType |*| OutboundType))
  def isPairOW: OutwardType -⚬ (OutwardType |+| (OutwardType |*| OutwardType))
  def recCall: (OutboundType |*| OutboundType) -⚬ OutboundType
  def recCallOW: (OutwardType |*| OutwardType) -⚬ OutwardType
  def isRecCall: OutboundType -⚬ (OutboundType |+| (OutboundType |*| OutboundType))
  def isRecCallOW: OutwardType -⚬ (OutwardType |+| (OutwardType |*| OutwardType))
  def eitherOW: (OutwardType |*| OutwardType) -⚬ OutwardType
  def intOW: Done -⚬ OutwardType
  def stringOW: Done -⚬ OutwardType
  def fixTOW[F[_]](F: TypeTag[F]): One -⚬ OutwardType
  def apply1TOW[F[_]](F: TypeTag[F]): OutwardType -⚬ OutwardType

  lazy val nested: Nested
}
