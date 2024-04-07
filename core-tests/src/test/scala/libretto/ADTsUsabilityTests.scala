package libretto

import libretto.testing.TestCase
import libretto.testing.scaletto.ScalettoTestKit
import libretto.testing.scalatest.scaletto.ScalatestScalettoTestSuite

class ADTsUsabilityTests extends ScalatestScalettoTestSuite {

  override def testCases(using kit: ScalettoTestKit): List[(String, TestCase[kit.type])] = {
    import kit.dsl.*
    import kit.dsl.given

    val coreLib = CoreLib(kit.dsl)
    import coreLib.{*, given}

    type NonEmptyTreeF[A, X] =
      OneOf[
        ("Leaf" of A) ::
        ("Branch" of (X |*| X)) ::
        Void
      ]

    type NonEmptyTree[A] =
      Rec[NonEmptyTreeF[A, _]]

    type Tree[A] =
      OneOf[
        ("Empty" of One) ::
        ("NonEmpty" of NonEmptyTree[A]) ::
        Void
      ]

    object NonEmptyTree {
      def pack[A]: NonEmptyTreeF[A, NonEmptyTree[A]] -⚬ NonEmptyTree[A] =
        dsl.pack

      def leaf[A]: A -⚬ NonEmptyTree[A] =
        OneOf.create[NonEmptyTreeF[A, NonEmptyTree[A]]].from["Leaf"] > pack[A]

      def branch[A]: (NonEmptyTree[A] |*| NonEmptyTree[A]) -⚬ NonEmptyTree[A] =
        OneOf.create[NonEmptyTreeF[A, NonEmptyTree[A]]].from["Branch"] > pack[A]
    }

    object Tree {
      def empty[A]: One -⚬ Tree[A] =
        OneOf.create[Tree[A]].from["Empty"]

      def single[A]: A -⚬ Tree[A] =
        NonEmptyTree.leaf[A] > OneOf.create[Tree[A]].from["NonEmpty"]
    }

    List()
  }

}
