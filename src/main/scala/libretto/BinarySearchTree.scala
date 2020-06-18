package libretto

object BinarySearchTree {
  def apply[DSL <: libretto.DSL](dsl0: DSL)(lib0: Lib[dsl0.type]): BinarySearchTree[DSL] =
    new BinarySearchTree[DSL] {
      val dsl: dsl0.type = dsl0
      val lib = lib0
    }
}

sealed trait BinarySearchTree[DSL <: libretto.DSL] {
  val dsl: DSL
  val lib: Lib[dsl.type]

  import dsl._
  import lib._
  import lib.Bool._
  import lib.Compare._

  sealed trait SummaryModule {
    type Summary[K]

    def singleton[K]: Val[K] -⚬ Summary[K]
    def merge[K]: (Summary[K] |*| Summary[K]) -⚬ Summary[K]
    def minKey[K]: Summary[K] -⚬ Val[K]
    def maxKey[K]: Summary[K] -⚬ Val[K]

    def dup[K]: Summary[K] -⚬ (Summary[K] |*| Summary[K])
    def discard[K]: Summary[K] -⚬ One

    implicit def summaryComonoid[K]: Comonoid[Summary[K]]
  }

  val Summary: SummaryModule = new SummaryModule {
    //                minKey |*| maxKey
    type Summary[K] = Val[K] |*| Val[K]

    def singleton[K]: Val[K] -⚬ Summary[K] =
      dsl.dup

    def minKey[K]: Summary[K] -⚬ Val[K] =
      discardSnd

    def maxKey[K]: Summary[K] -⚬ Val[K] =
      discardFst

    def merge[K]: (Summary[K] |*| Summary[K]) -⚬ Summary[K] =
      par(minKey, maxKey)

    def dup[K]: Summary[K] -⚬ (Summary[K] |*| Summary[K]) =
      par(dsl.dup[K], dsl.dup[K]) >>> IXI

    def discard[K]: Summary[K] -⚬ One =
      parToOne(dsl.discard, dsl.discard)

    def summaryComonoid[K]: Comonoid[Summary[K]] =
      new Comonoid[Summary[K]] {
        def counit: Summary[K] -⚬ One                         = discard
        def split : Summary[K] -⚬ (Summary[K] |*| Summary[K]) = dup
      }
  }

  import Summary.{Summary, summaryComonoid}

  sealed trait SingletonModule {
    type Singleton[K, V]

    def of[K, V]: (Val[K] |*| V) -⚬ Singleton[K, V]
    def deconstruct[K, V]: Singleton[K, V] -⚬ (Val[K] |*| V)
    def key[K, V]: Singleton[K, V] -⚬ (Val[K] |*| Singleton[K, V])
    def summary[K, V]: Singleton[K, V] -⚬ (Summary[K] |*| Singleton[K, V])
  }

  val Singleton: SingletonModule = new SingletonModule {
    type Singleton[K, V] = Val[K] |*| V

    def of[K, V]: (Val[K] |*| V) -⚬ Singleton[K, V] =
      id

    def deconstruct[K, V]: Singleton[K, V] -⚬ (Val[K] |*| V) =
      id

    def key[K, V]: Singleton[K, V] -⚬ (Val[K] |*| Singleton[K, V]) =
      getFst

    def summary[K, V]: Singleton[K, V] -⚬ (Summary[K] |*| Singleton[K, V]) =
      id[Singleton[K, V]]           .to[          Val[K]         |*| V  ]
        .in.fst(dup)                .to[ ( Val[K]   |*|  Val[K]) |*| V  ]
        .timesAssocLR               .to[   Val[K]   |*| (Val[K]  |*| V) ]
        .in.fst(Summary.singleton)  .to[ Summary[K] |*| (Val[K]  |*| V) ]
  }

  import Singleton.Singleton

  sealed trait BranchFModule {
    type BranchF[K, X]

    def of[K, X](summary: X -⚬ (Summary[K] |*| X)): (X |*| X) -⚬ BranchF[K, X]
    def deconstruct[K, X]: BranchF[K, X] -⚬ (X |*| X)
    def summary[K, X]: BranchF[K, X] -⚬ (Summary[K] |*| BranchF[K, X])
  }

  val BranchF: BranchFModule = new BranchFModule {
    type BranchF[K, X] = Summary[K] |*| (X |*| X)

    def of[K, X](summary: X -⚬ (Summary[K] |*| X)): (X |*| X) -⚬ BranchF[K, X] =
      id                              [                 X  |*|                 X  ]
        .par(summary, summary)     .to[ (Summary[K] |*| X) |*| (Summary[K] |*| X) ]
        .andThen(IXI)              .to[ (Summary[K] |*| Summary[K]) |*| (X |*| X) ]
        .in.fst(Summary.merge)     .to[         Summary[K]          |*| (X |*| X) ]

    def deconstruct[K, X]: BranchF[K, X] -⚬ (X |*| X) =
      discardFst

    def summary[K, X]: BranchF[K, X] -⚬ (Summary[K] |*| BranchF[K, X]) =
      id[BranchF[K, X]]            .to[          Summary[K]         |*| (X |*| X) ]
        .in.fst(Summary.dup)       .to[ (Summary[K] |*| Summary[K]) |*| (X |*| X) ]
        .timesAssocLR              .to[  Summary[K] |*|        BranchF[K, X]      ]
  }

  import BranchF.BranchF

  type NonEmptyTreeF[K, V, X] = Singleton[K, V] |+| BranchF[K, X]
  type NonEmptyTree[K, V] = Rec[NonEmptyTreeF[K, V, *]]

  type Branch[K, V] = BranchF[K, NonEmptyTree[K, V]]

  object Branch {
    def apply[K, V]: (NonEmptyTree[K, V] |*| NonEmptyTree[K, V]) -⚬ Branch[K, V] =
      BranchF.of(NonEmptyTree.summary)

    def deconstruct[K, V]: Branch[K, V] -⚬ (NonEmptyTree[K, V] |*| NonEmptyTree[K, V]) =
      BranchF.deconstruct

    def summary[K, V]: Branch[K, V] -⚬ (Summary[K] |*| Branch[K, V]) =
      BranchF.summary
  }

  object NonEmptyTree {
    def injectSingleton[K, V]: Singleton[K, V] -⚬ NonEmptyTree[K, V] =
      id[Singleton[K, V]]
        .injectL[Branch[K, V]]
        .pack[NonEmptyTreeF[K, V, *]]

    def injectBranch[K, V]: Branch[K, V] -⚬ NonEmptyTree[K, V] =
      id[Branch[K, V]]
        .injectR[Singleton[K, V]]
        .pack[NonEmptyTreeF[K, V, *]]

    def singleton[K, V]: (Val[K] |*| V) -⚬ NonEmptyTree[K, V] =
      Singleton.of[K, V] >>> injectSingleton

    def branch[K, V]: (NonEmptyTree[K, V] |*| NonEmptyTree[K, V]) -⚬ NonEmptyTree[K, V] =
      Branch[K, V] >>> injectBranch

    def summary[K, V]: NonEmptyTree[K, V] -⚬ (Summary[K] |*| NonEmptyTree[K, V]) =
      id                                                          [                           NonEmptyTree[K, V]                       ]
        .unpack[NonEmptyTreeF[K, V, *]]                        .to[                 Singleton[K, V]  |+|                 Branch[K, V]  ]
        .bimap(Singleton.summary[K, V], Branch.summary[K, V])  .to[ (Summary[K] |*| Singleton[K, V]) |+| (Summary[K] |*| Branch[K, V]) ]
        .andThen(factorL)                                      .to[  Summary[K] |*| (Singleton[K, V] |+|                 Branch[K, V]) ]
        .in.snd(pack[NonEmptyTreeF[K, V, *]])                  .to[  Summary[K] |*|         NonEmptyTree[K, V]                         ]

    def minKey[K, V]: NonEmptyTree[K, V] -⚬ (Val[K] |*| NonEmptyTree[K, V]) =
      summary[K, V] >>> par(Summary.minKey, id)

    def maxKey[K, V]: NonEmptyTree[K, V] -⚬ (Val[K] |*| NonEmptyTree[K, V]) =
      summary[K, V] >>> par(Summary.maxKey, id)

    def insert[K: Ordering, V]: ((Val[K] |*| V) |*| NonEmptyTree[K, V]) -⚬ (NonEmptyTree[K, V] |*| Maybe[V]) =
      rec { self =>
        id                                             [           (Val[K] |*| V) |*|         NonEmptyTree[K, V]                      ]
          .in.snd(unpack)                           .to[           (Val[K] |*| V) |*| (Singleton[K, V] |+| Branch[K, V])              ]
          .distributeLR                             .to[ ((Val[K] |*| V) |*| Singleton[K, V])  |+|  ((Val[K] |*| V) |*| Branch[K, V]) ]
          .either(sInsert[K, V], bInsert(self))     .to[                         NonEmptyTree[K, V] |*| Maybe[V]                      ]
      }

    /** Insert into singleton tree. */
    private def sInsert[K: Ordering, V]: ((Val[K] |*| V) |*| Singleton[K, V]) -⚬ (NonEmptyTree[K, V] |*| Maybe[V]) = {
      val intoR: ((Val[K] |*| V) |*| Singleton[K, V]) -⚬ (NonEmptyTree[K, V] |*| Maybe[V]) =
        id                                                       [     (Val[K] |*| V) |*| Singleton[K, V]    ]
          .swap                                               .to[    Singleton[K, V] |*|  (Val[K] |*| V)    ]
          .andThen(par(injectSingleton, singleton))           .to[ NonEmptyTree[K, V] |*| NonEmptyTree[K, V] ]
          .andThen(branch)                                    .to[            NonEmptyTree[K, V]             ]
          .introSnd                                           .to[       NonEmptyTree[K, V] |*| One          ]
          .in.snd(Maybe.empty[V])                             .to[       NonEmptyTree[K, V] |*| Maybe[V]     ]

      val intoL: ((Val[K] |*| V) |*| Singleton[K, V]) -⚬ (NonEmptyTree[K, V] |*| Maybe[V]) =
        id                                                       [   (Val[K] |*| V)   |*|   Singleton[K, V]  ]
          .andThen(par(singleton, injectSingleton))           .to[ NonEmptyTree[K, V] |*| NonEmptyTree[K, V] ]
          .andThen(branch)                                    .to[            NonEmptyTree[K, V]             ]
          .introSnd                                           .to[       NonEmptyTree[K, V] |*| One          ]
          .in.snd(Maybe.empty[V])                             .to[       NonEmptyTree[K, V] |*| Maybe[V]     ]

      val replace: ((Val[K] |*| V) |*| Singleton[K, V]) -⚬ (NonEmptyTree[K, V] |*| Maybe[V]) =
        id                                                       [   (Val[K] |*| V)   |*| Singleton[K, V]    ]
          .andThen(par(singleton, Singleton.deconstruct))     .to[ NonEmptyTree[K, V] |*|  (Val[K] |*| V)    ]
          .in.snd(discardFst)                                 .to[ NonEmptyTree[K, V] |*|              V     ]
          .in.snd(Maybe.just)                                 .to[ NonEmptyTree[K, V] |*|        Maybe[V]    ]

      id                                                         [   (Val[K] |*| V) |*| Singleton[K, V]      ]
        .andThen(compareBy(getFst, Singleton.key))            .to[ Compared[Val[K] |*| V, Singleton[K, V]]   ]
        .andThen(compared(intoL, replace, intoR))             .to[     NonEmptyTree[K, V] |*| Maybe[V]       ]
    }

    /** Insert into branch. */
    private def bInsert[K: Ordering, V](
      subInsert: ((Val[K] |*| V) |*| NonEmptyTree[K, V]) -⚬ (NonEmptyTree[K, V] |*| Maybe[V]),
    ): ((Val[K] |*| V) |*| Branch[K, V]) -⚬ (NonEmptyTree[K, V] |*| Maybe[V]) = {
      type Tree = NonEmptyTree[K, V]
      type Elem = Val[K] |*| V

      val insertL: ((Elem |*| Tree) |*| Tree) -⚬ (Tree |*| Maybe[V]) =
        id                                 [ (  Elem |*| Tree  ) |*| Tree ]
          .in.fst(subInsert)            .to[ (Tree |*| Maybe[V]) |*| Tree ]
          .andThen(IX)                  .to[ (Tree |*| Tree) |*| Maybe[V] ]
          .in.fst(branch)               .to[       Tree      |*| Maybe[V] ]

      val insertR: (Tree |*| (Elem |*| Tree)) -⚬ (Tree |*| Maybe[V]) =
        id                                 [ Tree |*| (  Elem |*| Tree  ) ]
          .in.snd(subInsert)            .to[ Tree |*| (Tree |*| Maybe[V]) ]
          .timesAssocRL                 .to[ (Tree |*| Tree) |*| Maybe[V] ]
          .in.fst(branch)               .to[       Tree      |*| Maybe[V] ]

      id                                   [                  Elem |*|         Branch[K, V]            ]
        .in.snd(Branch.deconstruct)     .to[                  Elem |*| (Tree                 |*| Tree) ]
        .timesAssocRL                   .to[                 (Elem |*| Tree)                 |*| Tree  ]
        .in.fst(lteqBy(getFst, maxKey)) .to[       (Bool |*| (Elem |*| Tree))                |*| Tree  ]
        .in.fst(ifThenElse(id, swap))   .to[ ((Elem |*| Tree)           |+| (Tree |*| Elem)) |*| Tree  ]
        .distributeRL                   .to[ ((Elem |*| Tree) |*| Tree) |+| ((Tree |*| Elem) |*| Tree) ]
        .in.right(timesAssocLR)         .to[ ((Elem |*| Tree) |*| Tree) |+| (Tree |*| (Elem |*| Tree)) ]
        .either(insertL, insertR)       .to[                     Tree |*| Maybe[V]                     ]
    }
  }

  type Tree[K, V] = One |+| NonEmptyTree[K, V]

  def empty[K, V]: One -⚬ Tree[K, V] =
    injectL

  def singleton[K, V]: (Val[K] |*| V) -⚬ Tree[K, V] =
    NonEmptyTree.singleton[K, V] >>> injectR

  def insert[K: Ordering, V]: ((Val[K] |*| V) |*| Tree[K, V]) -⚬ (Tree[K, V] |*| Maybe[V]) =
    id[(Val[K] |*| V) |*| Tree[K, V]]   .to[          (Val[K] |*| V) |*| (One |+| NonEmptyTree[K, V])              ]
      .distributeLR                     .to[ ((Val[K] |*| V) |*| One ) |+| ((Val[K] |*| V) |*| NonEmptyTree[K, V]) ]
      .in.right(NonEmptyTree.insert)    .to[ ((Val[K] |*| V) |*| One ) |+| (NonEmptyTree[K, V] |*|    Maybe[V]   ) ]
      .in.right.fst.injectR[One]        .to[ ((Val[K] |*| V) |*| One ) |+| (        Tree[K, V] |*|    Maybe[V]   ) ]
      .in.left.fst(singleton)           .to[ (Tree[K, V]     |*| One ) |+| (        Tree[K, V] |*|    Maybe[V]   ) ]
      .in.left.snd(Maybe.empty[V])      .to[ (Tree[K, V] |*| Maybe[V]) |+| (        Tree[K, V] |*|    Maybe[V]   ) ]
      .andThen(either(id, id))          .to[                  Tree[K, V] |*| Maybe[V]                              ]
}
