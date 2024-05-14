package libretto

import libretto.lambda.{Focus, Partitioning}
import libretto.lambda.util.{Applicative, SourcePos, TypeEqK}
import libretto.lambda.util.Monad.syntax.*
import libretto.testing.TestCase
import libretto.testing.scaletto.ScalettoTestKit
import libretto.testing.scalatest.scaletto.ScalatestScalettoTestSuite

class ADTsUsabilityTests extends ScalatestScalettoTestSuite {

  override def testCases(using kit: ScalettoTestKit): List[(String, TestCase[kit.type])] = {
    import kit.*
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

      def unpack[A]: NonEmptyTree[A] -⚬ NonEmptyTreeF[A, NonEmptyTree[A]] =
        dsl.unpack

      def leaf[A]: A -⚬ NonEmptyTree[A] =
        OneOf.create[NonEmptyTreeF[A, NonEmptyTree[A]]].from["Leaf"] > pack[A]

      def branch[A]: (NonEmptyTree[A] |*| NonEmptyTree[A]) -⚬ NonEmptyTree[A] =
        OneOf.create[NonEmptyTreeF[A, NonEmptyTree[A]]].from["Branch"] > pack[A]

      def foldMap[A, B](f: A -⚬ B, g: (B |*| B) -⚬ B): NonEmptyTree[A] -⚬ B =
        rec { self =>
          unpack[A] > OneOf.switch(_
            .caseOf["Leaf"](f)
            .caseOf["Branch"](par(self, self) > g)
            .end
          )
        }
    }

    object Tree {
      def empty[A]: One -⚬ Tree[A] =
        OneOf.create[Tree[A]].from["Empty"]

      def nonEmpty[A]: NonEmptyTree[A] -⚬ Tree[A] =
        OneOf.create[Tree[A]].from["NonEmpty"]

      def single[A]: A -⚬ Tree[A] =
        NonEmptyTree.leaf[A] > nonEmpty

      def branch[A]: (NonEmptyTree[A] |*| NonEmptyTree[A]) -⚬ Tree[A] =
        NonEmptyTree.branch[A] > nonEmpty

      def foldMap[A, B](f: A -⚬ B, g: (B |*| B) -⚬ B): Tree[A] -⚬ Maybe[B] =
        OneOf.switch[Tree[A]](_
          .caseOf["Empty"](Maybe.empty[B])
          .caseOf["NonEmpty"](NonEmptyTree.foldMap(f, g) > Maybe.just)
          .end
        )

      def concat[A]: (Tree[A] |*| Tree[A]) -⚬ Tree[A] =
        λ { case t1 |*| t2 =>
          (t1 |*| t2) :>> OneOf.distLR :>> OneOf.switch(_
            .caseOf["Empty"](elimSnd)
            .caseOf["NonEmpty"](λ { case t1 |*| net2 =>
              ((net2 |*| t1) :>> OneOf.distLR).switch(_
                .caseOf["Empty"](elimSnd)
                .caseOf["NonEmpty"](λ { case (net2 |*| net1) => NonEmptyTree.branch(net1 |*| net2) })
                .end
              ) :>> nonEmpty
            })
            .end
          )
        }

      def partitioning[A]: Partitioning[-⚬, |*|, Tree[A]] =
        new PartitioningImpl

      private sealed trait PartitionImpl[A, B]
      private object PartitionImpl {
        case class Empty[A]() extends PartitionImpl[A, One]
        case class NonEmpty[A]() extends PartitionImpl[A, NonEmptyTree[A]]
      }

      private class PartitioningImpl[A] extends Partitioning[-⚬, |*|, Tree[A]] {
        final override type Partition[B] = PartitionImpl[A, B]

        private def dsl = kit.dsl

        override def compileAt[F[_], G[_], R](
          pos: Focus[|*|, F],
          handle: [X] => Partition[X] => G[F[X] -⚬ R],
        )(using
          G: Applicative[G],
        ): G[F[Tree[A]] -⚬ R] =
          G.map2(
            handle(PartitionImpl.Empty[A]()),
            handle(PartitionImpl.NonEmpty[A]()),
          ) { (handleEmpty, handleNonEmpty) =>
            id[F[Tree[A]]] > OneOf.distF(using pos) > OneOf.switch(_
              .caseOf["Empty"](handleEmpty)
              .caseOf["NonEmpty"](handleNonEmpty)
              .end
            )
          }

        override def isTotal[P](p: Partition[P]): Option[Tree[A] -⚬ P] =
          libretto.lambda.UnhandledCase.raise("isTotal")

        override def sameAs(that: Partitioning[-⚬, |*|, Tree[A]]): Option[TypeEqK[this.Partition, that.Partition]] =
          that match
            case that1: (PartitioningImpl[A] & that.type) if (that1.dsl eq this.dsl) =>
              Some(TypeEqK.refl[this.Partition]): Option[TypeEqK[this.Partition, that1.Partition]]
            case _ =>
              None
      }

      private object PartitioningImpl {
        def apply[A]: PartitioningImpl[A] =
          new PartitioningImpl[A]
      }

      object Empty {
        def unapply[A](x: $[Tree[A]])(using pos: SourcePos, ctx: LambdaContext): Some[$[One]] =
          Some($.matchAgainst(x, PartitioningImpl[A].partition(PartitionImpl.Empty[A]()))(pos))
      }

      object NonEmpty {
        def unapply[A](x: $[Tree[A]])(using pos: SourcePos, ctx: LambdaContext): Some[$[NonEmptyTree[A]]] =
          Some($.matchAgainst(x, PartitioningImpl[A].partition(PartitionImpl.NonEmpty[A]()))(pos))
      }
    }

    List(
      "create and fold Tree" ->
        TestCase.interactWith {
          import NonEmptyTree.{leaf, branch}
          λ { case +(d) =>
            val tree =
              Tree.branch(
                branch(leaf(d :>> constVal(1)) |*| leaf(d :>> constVal(2))) |*|
                branch(leaf(d :>> constVal(3)) |*| leaf(d :>> constVal(4)))
              )
            tree
              :>> Tree.foldMap(id, unliftPair > mapVal { case (a, b) => a + b })
              :>> Maybe.getOrElse(done > constVal(0))
          }
        }.via { port =>
          for {
            n <- expectVal(port)
            _ <- Outcome.assertEquals(n, 10)
          } yield ()
        },

      "concatenate trees" ->
        TestCase.interactWith {
          import NonEmptyTree.{leaf, branch}
          λ { case +(d) =>
            val tree1 =
              Tree.nonEmpty(branch(leaf(d :>> constVal(1)) |*| leaf(d :>> constVal(2))))
            val tree2 =
              Tree.nonEmpty(branch(leaf(d :>> constVal(3)) |*| leaf(d :>> constVal(4))))
            val tree =
              Tree.concat(tree1 |*| tree2)
            tree
              :>> Tree.foldMap(mapVal(_.toString), unliftPair > mapVal { case (a, b) => s"$a,$b" })
              :>> Maybe.getOrElse(done > constVal(""))
          }
        }.via { port =>
          for {
            s <- expectVal(port)
            _ <- Outcome.assertEquals(s, "1,2,3,4")
          } yield ()
        }
    )
  }

}
