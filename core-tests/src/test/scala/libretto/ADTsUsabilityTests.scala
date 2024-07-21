package libretto

import libretto.lambda.{Extractor, Focus, Partitioning}
import libretto.lambda.util.{Applicative, SourcePos, TypeEqK}
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
    import dsl.{|| as |}

    type Maybe[A] = OneOf
      [ "Empty" :: One
      | "Just" :: A
      ]

    object Maybe {
      def Empty[A]: Extractor[-⚬, |*|, Maybe[A], One] = OneOf.partition[Maybe[A]]["Empty"]
      def Just[A]:  Extractor[-⚬, |*|, Maybe[A], A]   = OneOf.partition[Maybe[A]]["Just"]

      def getOrElse[A](ifEmpty: One -⚬ A): Maybe[A] -⚬ A =
        λ { ma =>
          switch(ma)
            .is { case Just(a) => a }
            .is { case Empty(unit) => ifEmpty(unit) }
            .end
        }
    }

    type NonEmptyTreeF[A, X] = OneOf
      [ "Leaf" :: A
      | "Branch" :: (X |*| X)
      ]

    type NonEmptyTree[A] =
      Rec[NonEmptyTreeF[A, _]]

    object NonEmptyTree {
      def Leaf[A]: Extractor[-⚬, |*|, NonEmptyTree[A], A] =
        OneOf.partition[NonEmptyTreeF[A, NonEmptyTree[A]]]["Leaf"].afterUnpack

      def Branch[A]: Extractor[-⚬, |*|, NonEmptyTree[A], NonEmptyTree[A] |*| NonEmptyTree[A]] =
        OneOf.partition[NonEmptyTreeF[A, NonEmptyTree[A]]]["Branch"].afterUnpack

      /** `foldMap` using barebones handling of cases in order. */
      def foldMapBB[A, B](f: A -⚬ B, g: (B |*| B) -⚬ B): NonEmptyTree[A] -⚬ B =
        rec { self =>
          unpack > OneOf.handle(_
            .caseOf["Branch"](par(self, self) > g)
            .caseOf["Leaf"](f)
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
              .is { case Leaf(a) => Leaf(a) }
              .is { case Branch(l |*| Leaf(a)) => Branch(self(l) |*| Leaf(a)) }
              .is { case Branch(l |*| Branch(rl |*| rr)) => self(Branch(Branch(l |*| rl) |*| rr)) }
              .end
          }
        }

      /** `skewLeft` using nested `switch`s (instead of nested patterns). */
      def skewLeftNS[A]: NonEmptyTree[A] -⚬ NonEmptyTree[A] =
        rec { self =>
          λ { t =>
            switch(t)
              .is { case Leaf(a) => Leaf(a) }
              .is { case Branch(l |*| r) =>
                switch(r)
                  .is { case Leaf(a) => Branch(self(l) |*| Leaf(a)) }
                  .is { case Branch(rl |*| rr) => self(Branch(Branch(l |*| rl) |*| rr)) }
                  .end
              }
              .end
          }
        }

      def skewRight[A]: NonEmptyTree[A] -⚬ NonEmptyTree[A] =
        rec { self =>
          λ { t =>
            switch(t)
              .is { case Branch(Branch(ll |*| lr) |*| r) => self(Branch(ll |*| Branch(lr |*| r))) }
              .is { case Branch(Leaf(a) |*| r) => Branch(Leaf(a) |*| self(r)) }
              .is { case Leaf(a) => Leaf(a) }
              .end
          }
        }

      /** `skewRight` using nested `switch`s (instead of nested patterns). */
      def skewRightNS[A]: NonEmptyTree[A] -⚬ NonEmptyTree[A] =
        rec { self =>
          λ { t =>
            switch(t)
              .is { case Branch(l |*| r) =>
                switch(l)
                  .is { case Branch(ll |*| lr) => self(Branch(ll |*| Branch(lr |*| r))) }
                  .is { case Leaf(a) => Branch(Leaf(a) |*| self(r)) }
                  .end
              }
              .is { case Leaf(a) => Leaf(a) }
              .end
          }
        }

      def print[A](f: A -⚬ Val[String]): NonEmptyTree[A] -⚬ Val[String] =
        foldMap(f, unliftPair > mapVal { case (l, r) => s"($l, $r)" })
    }

    type Tree[A] = OneOf
      [ "Empty" :: One
      | "NonEmpty" :: NonEmptyTree[A]
      ]

    object Tree {
      def Empty[A]:    Extractor[-⚬, |*|, Tree[A], One]             = OneOf.partition[Tree[A]]["Empty"]
      def NonEmpty[A]: Extractor[-⚬, |*|, Tree[A], NonEmptyTree[A]] = OneOf.partition[Tree[A]]["NonEmpty"]

      def single[A]: A -⚬ Tree[A] =
        NonEmptyTree.Leaf[A]() > NonEmpty()

      def branch[A]: (NonEmptyTree[A] |*| NonEmptyTree[A]) -⚬ Tree[A] =
        NonEmptyTree.Branch[A]() > NonEmpty()

      /** `foldMap` using barebones handling of cases in order. */
      def foldMapBB[A, B](f: A -⚬ B, g: (B |*| B) -⚬ B): Tree[A] -⚬ Maybe[B] =
        OneOf.handle[Tree[A]](_
          .caseOf["NonEmpty"](NonEmptyTree.foldMapBB(f, g) > Maybe.Just())
          .caseOf["Empty"](Maybe.Empty[B]())
        )

      def foldMap[A, B](f: A -⚬ B, g: (B |*| B) -⚬ B): Tree[A] -⚬ Maybe[B] =
        λ { ta =>
          switch(ta)
            .is { case Empty(u)     => Maybe.Empty[B](u) }
            .is { case NonEmpty(ta) => Maybe.Just(NonEmptyTree.foldMap(f, g)(ta)) }
            .end
        }

      /** `concat` using barebones handling of cases in order. */
      def concatBB[A]: (Tree[A] |*| Tree[A]) -⚬ Tree[A] =
        λ { case t1 |*| t2 =>
          (t1 |*| t2) :>> OneOf.distLR :>> OneOf.handle(_
            .caseOf["NonEmpty"](λ { case t1 |*| net2 =>
              ((net2 |*| t1) :>> OneOf.distLR) :>> OneOf.handle(_
                .caseOf["NonEmpty"](λ { case (net2 |*| net1) => NonEmptyTree.Branch(net1 |*| net2) })
                .caseOf["Empty"](elimSnd)
              ) :>> NonEmpty()
            })
            .caseOf["Empty"](elimSnd)
          )
        }

      def concat[A]: (Tree[A] |*| Tree[A]) -⚬ Tree[A] =
        λ { case t1 |*| t2 =>
          switch(t1 |*| t2)
            .is { case Empty(?(_)) |*| t2 => t2 }
            .is { case t1 |*| Empty(?(_)) => t1 }
            .is { case NonEmpty(t1) |*| NonEmpty(t2) => branch(t1 |*| t2) }
            .end
        }

      /** `concat` using nested `switch`s (instead of nested patterns). */
      def concatNS[A]: (Tree[A] |*| Tree[A]) -⚬ Tree[A] =
        λ { case t1 |*| t2 =>
          switch(t2)
            .is { case Empty(?(_)) => t1 }
            .is { case NonEmpty(t2) =>
              switch(t1)
                .is { case Empty(?(_)) => NonEmpty(t2) }
                .is { case NonEmpty(t1) => branch(t1 |*| t2) }
                .end
            }
            .end
        }

      def skewLeft[A]: Tree[A] -⚬ Tree[A] =
        λ { t =>
          switch(t)
            .is { case Empty(u) => Empty(u) }
            .is { case NonEmpty(t) => NonEmpty(NonEmptyTree.skewLeft(t)) }
            .end
        }

      def skewRight[A]: Tree[A] -⚬ Tree[A] =
        λ { t =>
          switch(t)
            .is { case Empty(u) => Empty(u) }
            .is { case NonEmpty(t) => NonEmpty(NonEmptyTree.skewRight(t)) }
            .end
        }

      def print[A](f: A -⚬ Val[String]): Tree[A] -⚬ Val[String] =
        foldMap(f, unliftPair > mapVal { case (l, r) => s"($l, $r)" })
          > Maybe.getOrElse(done > constVal("()"))
    }

    def c[A](using d: $[Done])(a: A)(using LambdaContext, SourcePos): $[NonEmptyTree[Val[A]]] =
      d :>> constVal(a) :>> NonEmptyTree.Leaf()

    extension [A](t: $[NonEmptyTree[A]]) {
      def ++(u: $[NonEmptyTree[A]])(using LambdaContext, SourcePos): $[NonEmptyTree[A]] =
        (t |*| u) :>> NonEmptyTree.Branch()
    }

    List(
      "foldMapBB" -> Tree.foldMapBB[Val[Int], Val[Int]],
      "foldMap" -> Tree.foldMap[Val[Int], Val[Int]],
    ).map { case (desc, foldMap) =>

      s"create and fold Tree ($desc)" ->
        TestCase.interactWith {
          import NonEmptyTree.{Leaf, Branch}
          λ { case +(d) =>
            given $[Done] = d
            val tree =
              Tree.NonEmpty((c(1) ++ c(2)) ++ (c(3) ++ c(4)))
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
      "concatNS" -> Tree.concatNS[Val[Int]],
    ).map { case (desc, concat) =>

      s"concatenate trees ($desc)" ->
        TestCase.interactWith {
          import NonEmptyTree.{Leaf, Branch}
          λ { case +(d) =>
            given $[Done] = d
            val tree1 = Tree.NonEmpty(c(1) ++ c(2))
            val tree2 = Tree.NonEmpty(c(3) ++ c(4))
            val tree  = concat(tree1 |*| tree2)
            tree :>> Tree.print(mapVal(_.toString))
          }
        }.via { port =>
          for {
            s <- expectVal(port)
            _ <- Outcome.assertEquals(s, "((1, 2), (3, 4))")
          } yield ()
        }

    } ++ List(
      ("skewLeft, skewRight") -> (NonEmptyTree.skewLeft[Val[Int]], NonEmptyTree.skewRight[Val[Int]]),
      ("skewLeftNS, skewRightNS") -> (NonEmptyTree.skewLeftNS[Val[Int]], NonEmptyTree.skewRightNS[Val[Int]]),
    ).map { case (desc, (skewLeft, skewRight)) =>

       s"skew trees ($desc)" -> TestCase
        .interactWith {
          import NonEmptyTree.{Leaf, Branch}

          λ { case +(d) =>
            given $[Done] = d
            val tree1, tree2 = (c(1) ++ c(2)) ++ (c(3) ++ c(4))
            val s1 = skewLeft (tree1) :>> NonEmptyTree.print(mapVal(_.toString))
            val s2 = skewRight(tree2) :>> NonEmptyTree.print(mapVal(_.toString))
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

    }
  }

}
