package libretto

import libretto.lambda.{Focus, Partitioning}
import libretto.lambda.util.{Applicative, SourcePos, TypeEqK}
import libretto.lambda.util.Monad.syntax.*
import libretto.testing.TestCase
import libretto.testing.scaletto.ScalettoTestKit
import libretto.testing.scalatest.scaletto.ScalatestScalettoTestSuite

class ADTsUsabilityTests extends ScalatestScalettoTestSuite {

  override def testCases(using kit: ScalettoTestKit): List[(String, TestCase[kit.type])] = {
    import kit.{OutPort as _, *}
    import kit.dsl.*
    import kit.dsl.given

    val coreLib = CoreLib(kit.dsl)
    import coreLib.{*, given}

    type NonEmptyTreeF[A, X] =
      OneOf[
        ("Leaf" of A) ::
        ("Branch" of (X |*| X))
      ]

    type NonEmptyTree[A] =
      Rec[NonEmptyTreeF[A, _]]

    type Tree[A] =
      OneOf[
        ("Empty" of One) ::
        ("NonEmpty" of NonEmptyTree[A])
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

      object Leaf {
        def unapply[A](x: $[NonEmptyTree[A]])(using pos: SourcePos, ctx: LambdaContext): Some[$[A]] =
          Some(x.unpackedMatchAgainst(OneOf.partition[NonEmptyTreeF[A, NonEmptyTree[A]]]["Leaf"]))
      }

      object Branch {
        def unapply[A](x: $[NonEmptyTree[A]])(using pos: SourcePos, ctx: LambdaContext): Some[$[NonEmptyTree[A] |*| NonEmptyTree[A]]] =
          Some(x.unpackedMatchAgainst(OneOf.partition[NonEmptyTreeF[A, NonEmptyTree[A]]]["Branch"]))
      }

      /** `foldMap` using barebones handling of cases in order. */
      def foldMapBB[A, B](f: A -⚬ B, g: (B |*| B) -⚬ B): NonEmptyTree[A] -⚬ B =
        rec { self =>
          unpack[A] > OneOf.handle(_
            .caseOf["Leaf"](f)
            .caseOf["Branch"](par(self, self) > g)
          )
        }

      def foldMap[A, B](f: A -⚬ B, g: (B |*| B) -⚬ B): NonEmptyTree[A] -⚬ B =
        rec { self =>
          λ { ta =>
            switch(ta)
              .is { case Leaf(a) => f(a) }
              .is { case Branch(l |*| r) => g(self(l) |*| self(r)) }
              .end
          }
        }

      def skewLeft[A]: NonEmptyTree[A] -⚬ NonEmptyTree[A] =
        rec { self =>
          λ { t =>
            switch(t)
              .is { case Leaf(a) => leaf(a) }
              .is { case Branch(l |*| Leaf(a)) => branch(self(l) |*| leaf(a)) }
              .is { case Branch(l |*| Branch(rl |*| rr)) => self(branch(branch(l |*| rl) |*| rr)) }
              .end
          }
        }

      def skewRight[A]: NonEmptyTree[A] -⚬ NonEmptyTree[A] =
        rec { self =>
          λ { t =>
            switch(t)
              .is { case Branch(Branch(ll |*| lr) |*| r) => self(branch(ll |*| branch(lr |*| r))) }
              .is { case Branch(Leaf(a) |*| r) => branch(leaf(a) |*| self(r)) }
              .is { case Leaf(a) => leaf(a) }
              .end
          }
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

      /** `foldMap` using barebones handling of cases in order. */
      def foldMapBB[A, B](f: A -⚬ B, g: (B |*| B) -⚬ B): Tree[A] -⚬ Maybe[B] =
        OneOf.handle[Tree[A]](_
          .caseOf["Empty"](Maybe.empty[B])
          .caseOf["NonEmpty"](NonEmptyTree.foldMapBB(f, g) > Maybe.just)
        )

      def foldMap[A, B](f: A -⚬ B, g: (B |*| B) -⚬ B): Tree[A] -⚬ Maybe[B] =
        λ { ta =>
          switch(ta)
            .is { case Empty(u)     => Maybe.empty[B](u) }
            .is { case NonEmpty(ta) => Maybe.just(NonEmptyTree.foldMap(f, g)(ta)) }
            .end
        }

      /** `concat` using barebones handling of cases in order. */
      def concatBB[A]: (Tree[A] |*| Tree[A]) -⚬ Tree[A] =
        λ { case t1 |*| t2 =>
          (t1 |*| t2) :>> OneOf.distLR :>> OneOf.handle(_
            .caseOf["Empty"](elimSnd)
            .caseOf["NonEmpty"](λ { case t1 |*| net2 =>
              ((net2 |*| t1) :>> OneOf.distLR).handle(_
                .caseOf["Empty"](elimSnd)
                .caseOf["NonEmpty"](λ { case (net2 |*| net1) => NonEmptyTree.branch(net1 |*| net2) })
              ) :>> nonEmpty
            })
          )
        }

      def concat[A]: (Tree[A] |*| Tree[A]) -⚬ Tree[A] =
        λ { case t1 |*| t2 =>
          switch(t1 |*| t2)
            .is { case Empty(?(_)) |*| t2 => t2 }
            .is { case t1 |*| Empty(?(_)) => t1 }
            .is { case NonEmpty(t1) |*| NonEmpty(t2) => nonEmpty(NonEmptyTree.branch(t1 |*| t2)) }
            .end
        }

      def skewLeft[A]: Tree[A] -⚬ Tree[A] =
        λ { t =>
          switch(t)
            .is { case Empty(u) => empty(u) }
            .is { case NonEmpty(t) => nonEmpty(NonEmptyTree.skewLeft(t)) }
            .end
        }

      def skewRight[A]: Tree[A] -⚬ Tree[A] =
        λ { t =>
          switch(t)
            .is { case Empty(u) => empty(u) }
            .is { case NonEmpty(t) => nonEmpty(NonEmptyTree.skewRight(t)) }
            .end
        }

      def print[A](f: A -⚬ Val[String]): Tree[A] -⚬ Val[String] =
        foldMap(f, unliftPair > mapVal { case (l, r) => s"($l, $r)" })
          > Maybe.getOrElse(done > constVal("()"))

      object Empty {
        def unapply[A](x: $[Tree[A]])(using pos: SourcePos, ctx: LambdaContext): Some[$[One]] =
          Some(x.matchAgainst("Empty"))
      }

      object NonEmpty {
        def unapply[A](x: $[Tree[A]])(using pos: SourcePos, ctx: LambdaContext): Some[$[NonEmptyTree[A]]] =
          Some(x.matchAgainst("NonEmpty"))
      }
    }

    List(
      "foldMapBB" -> Tree.foldMapBB[Val[Int], Val[Int]],
      "foldMap" -> Tree.foldMap[Val[Int], Val[Int]],
    ).map { case (desc, foldMap) =>

      s"create and fold Tree ($desc)" ->
        TestCase.interactWith {
          import NonEmptyTree.{leaf, branch}
          λ { case +(d) =>
            val tree =
              Tree.branch(
                branch(leaf(d :>> constVal(1)) |*| leaf(d :>> constVal(2))) |*|
                branch(leaf(d :>> constVal(3)) |*| leaf(d :>> constVal(4)))
              )
            tree
              :>> foldMap(id, unliftPair > mapVal { case (a, b) => a + b })
              :>> Maybe.getOrElse(done > constVal(0))
          }
        }.via { port =>
          for {
            n <- expectVal(port)
            _ <- Outcome.assertEquals(n, 10)
          } yield ()
        }

    } ++ List(
      "concatBB" -> Tree.concatBB[Val[Int]],
      "concat" -> Tree.concat[Val[Int]],
    ).map { case (desc, concat) =>

      s"concatenate trees ($desc)" ->
        TestCase.interactWith {
          import NonEmptyTree.{leaf, branch}
          λ { case +(d) =>
            val tree1 =
              Tree.nonEmpty(branch(leaf(d :>> constVal(1)) |*| leaf(d :>> constVal(2))))
            val tree2 =
              Tree.nonEmpty(branch(leaf(d :>> constVal(3)) |*| leaf(d :>> constVal(4))))
            val tree =
              concat(tree1 |*| tree2)
            tree
              :>> Tree.foldMapBB(mapVal(_.toString), unliftPair > mapVal { case (a, b) => s"$a,$b" })
              :>> Maybe.getOrElse(done > constVal(""))
          }
        }.via { port =>
          for {
            s <- expectVal(port)
            _ <- Outcome.assertEquals(s, "1,2,3,4")
          } yield ()
        }

    } ++ List(
      "skewLeft, skewRight" -> TestCase
        .interactWith {
          import NonEmptyTree.{leaf, branch}

          λ { case +(d) =>
            val tree1, tree2 =
              Tree.branch(
                branch(leaf(d :>> constVal(1)) |*| leaf(d :>> constVal(2))) |*|
                branch(leaf(d :>> constVal(3)) |*| leaf(d :>> constVal(4)))
              )
            val s1 = Tree.skewLeft (tree1) :>> Tree.print(mapVal(_.toString))
            val s2 = Tree.skewRight(tree2) :>> Tree.print(mapVal(_.toString))
            s1 |*| s2
          }
        }
        .via { port =>
          val (p1, p2) = OutPort.split(port)
          for {
            s1 <- expectVal(p1)
            s2 <- expectVal(p2)
            _ <- Outcome.assertEquals(s1, "(((1, 2), 3), 4)")
            _ <- Outcome.assertEquals(s2, "(1, (2, (3, 4)))")
          } yield ()
        }
    )
  }

}
