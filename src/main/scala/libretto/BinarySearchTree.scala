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

    private[BinarySearchTree] def update_[K: Ordering, V, W, F[_]](
      ins:         W -⚬ F[V],
      upd: (W |*| V) -⚬ F[V],
    )(implicit
      F: Once[F],
    ): ((Val[K] |*| W) |*| NonEmptyTree[K, V]) -⚬ F[NonEmptyTree[K, V]] = 
      rec { self =>
        id                                             [           (Val[K] |*| W) |*|         NonEmptyTree[K, V]                      ]
          .in.snd(unpack)                           .to[           (Val[K] |*| W) |*| (Singleton[K, V] |+| Branch[K, V])              ]
          .distributeLR                             .to[ ((Val[K] |*| W) |*| Singleton[K, V])  |+|  ((Val[K] |*| W) |*| Branch[K, V]) ]
          .in.left(sUpdate(ins, upd))               .to[       F[NonEmptyTree[K, V]]           |+|  ((Val[K] |*| W) |*| Branch[K, V]) ]
          .in.right(bUpdate(self))                  .to[       F[NonEmptyTree[K, V]]           |+|        F[NonEmptyTree[K, V]]       ]
          .andThen(either(id, id))                  .to[                             F[NonEmptyTree[K, V]]                            ]
      }

    /** Update singleton tree. */
    private def sUpdate[K: Ordering, V, W, F[_]](
      ins:         W -⚬ F[V],
      upd: (W |*| V) -⚬ F[V],
    )(implicit
      F: Once[F],
    ): ((Val[K] |*| W) |*| Singleton[K, V]) -⚬ F[NonEmptyTree[K, V]] = {
      val intoR: ((Val[K] |*| W) |*| Singleton[K, V]) -⚬ F[NonEmptyTree[K, V]] =
        id                                                       [     (Val[K] |*| W) |*|    Singleton[K, V]    ]
          .swap                                               .to[    Singleton[K, V] |*|  (  Val[K] |*|   W  ) ]
          .in.snd.snd(ins)                                    .to[    Singleton[K, V] |*|  (  Val[K] |*| F[V] ) ]
          .in.snd(F.captureL)                                 .to[    Singleton[K, V] |*| F[  Val[K] |*|   V  ] ]
          .andThen(par(injectSingleton, F.lift(singleton)))   .to[ NonEmptyTree[K, V] |*| F[NonEmptyTree[K, V]] ]
          .andThen(F.captureL)                                .to[ F[NonEmptyTree[K, V] |*| NonEmptyTree[K, V]] ]
          .andThen(F.lift(branch))                            .to[            F[NonEmptyTree[K, V]]             ]

      val intoL: ((Val[K] |*| W) |*| Singleton[K, V]) -⚬ F[NonEmptyTree[K, V]] =
        id                                                       [  (Val[K] |*|  W  )    |*|   Singleton[K, V]  ]
          .in.fst.snd(ins)                                    .to[  (Val[K] |*| F[V])    |*|   Singleton[K, V]  ]
          .in.fst(F.captureL)                                 .to[ F[Val[K] |*|   V ]    |*|   Singleton[K, V]  ]
          .andThen(par(F.lift(singleton), injectSingleton))   .to[ F[NonEmptyTree[K, V]] |*| NonEmptyTree[K, V] ]
          .andThen(F.captureR)                                .to[ F[NonEmptyTree[K, V] |*| NonEmptyTree[K, V]] ]
          .andThen(F.lift(branch))                            .to[             F[NonEmptyTree[K, V]]            ]

      val replace: ((Val[K] |*| W) |*| Singleton[K, V]) -⚬ F[NonEmptyTree[K, V]] =
        id                                                       [ (Val[K] |*| W) |*| Singleton[K, V] ]
          .andThen(par(discardFst, Singleton.deconstruct))    .to[             W  |*|  (Val[K] |*| V) ]
          .andThen(XI)                                        .to[         Val[K] |*|       (W |*| V) ]
          .in.snd(upd)                                        .to[         Val[K] |*|            F[V] ]
          .andThen(F.captureL)                                .to[       F[Val[K] |*|              V] ]
          .andThen(F.lift(singleton))                         .to[        F[NonEmptyTree[K, V]]       ]

      id                                                         [   (Val[K] |*| W) |*| Singleton[K, V]    ]
        .andThen(compareBy(getFst, Singleton.key))            .to[ Compared[Val[K] |*| W, Singleton[K, V]] ]
        .andThen(compared(intoL, replace, intoR))             .to[        F[NonEmptyTree[K, V]]            ]
    }

    /** Update branch. */
    private def bUpdate[K: Ordering, V, W, F[_]](
      subUpdate: ((Val[K] |*| W) |*| NonEmptyTree[K, V]) -⚬ F[NonEmptyTree[K, V]],
    )(implicit
      F: Once[F],
    ): ((Val[K] |*| W) |*| Branch[K, V]) -⚬ F[NonEmptyTree[K, V]] = {
      type Tree = NonEmptyTree[K, V]
      type Elem = Val[K] |*| W

      val updateL: ((Elem |*| Tree) |*| Tree) -⚬ F[Tree] =
        id                                 [ (Elem |*| Tree) |*| Tree  ]
          .in.fst(subUpdate)            .to[    F[Tree]      |*| Tree  ]
          .andThen(F.captureR)          .to[    F[Tree       |*| Tree] ]
          .andThen(F.lift(branch))      .to[    F[          Tree     ] ]

      val updateR: (Tree |*| (Elem |*| Tree)) -⚬ F[Tree] =
        id                                 [   Tree |*| (Elem |*| Tree) ]
          .in.snd(subUpdate)            .to[   Tree |*|     F[Tree]     ]
          .andThen(F.captureL)          .to[ F[Tree |*|       Tree]     ]
          .andThen(F.lift(branch))      .to[ F[     Tree          ]     ]

      id                                   [                  Elem |*|         Branch[K, V]            ]
        .in.snd(Branch.deconstruct)     .to[                  Elem |*| (Tree                 |*| Tree) ]
        .timesAssocRL                   .to[                 (Elem |*| Tree)                 |*| Tree  ]
        .in.fst(lteqBy(getFst, maxKey)) .to[       (Bool |*| (Elem |*| Tree))                |*| Tree  ]
        .in.fst(ifThenElse(id, swap))   .to[ ((Elem |*| Tree)           |+| (Tree |*| Elem)) |*| Tree  ]
        .distributeRL                   .to[ ((Elem |*| Tree) |*| Tree) |+| ((Tree |*| Elem) |*| Tree) ]
        .in.right(timesAssocLR)         .to[ ((Elem |*| Tree) |*| Tree) |+| (Tree |*| (Elem |*| Tree)) ]
        .either(updateL, updateR)       .to[                          F[Tree]                          ]
    }
  }

  type Tree[K, V] = One |+| NonEmptyTree[K, V]

  def empty[K, V]: One -⚬ Tree[K, V] =
    injectL

  def singleton[K, V]: (Val[K] |*| V) -⚬ Tree[K, V] =
    NonEmptyTree.singleton[K, V] >>> injectR

  private def update_[K: Ordering, V, W, F[_]](
    ins:         W -⚬ F[V],
    upd: (W |*| V) -⚬ F[V],
  )(implicit
    F: Once[F],
  ): ((Val[K] |*| W) |*| Tree[K, V]) -⚬ F[Tree[K, V]] = {
    val NET = NonEmptyTree
    type NET[K, V] = NonEmptyTree[K, V]

    id[(Val[K] |*| W) |*| Tree[K, V]]   .to[          (Val[K] |*| W) |*| (One |+| NET[K, V])                ]
      .distributeLR                     .to[ ((Val[K] |*|  W  ) |*| One) |+| ((Val[K] |*| W) |*| NET[K, V]) ]
      .in.right(NET.update_(ins, upd))  .to[ ((Val[K] |*|  W  ) |*| One) |+|           F[ NET[K, V]]        ]
      .in.right.co[F].injectR[One]      .to[ ((Val[K] |*|  W  ) |*| One) |+|           F[Tree[K, V]]        ]
      .in.left(elimSnd)                 .to[  (Val[K] |*|  W  )          |+|           F[Tree[K, V]]        ]
      .in.left.snd(ins)                 .to[  (Val[K] |*| F[V])          |+|           F[Tree[K, V]]        ]
      .in.left(F.captureL)              .to[   F[Val[K] |*| V]           |+|           F[Tree[K, V]]        ]
      .in.left(F.lift(singleton))       .to[   F[ Tree[K, V] ]           |+|           F[Tree[K, V]]        ]
      .andThen(either(id, id))          .to[                        F[Tree[K, V]]                                    ]
  }

  def insert[K: Ordering, V]: ((Val[K] |*| V) |*| Tree[K, V]) -⚬ (Maybe[V] |*| Tree[K, V]) =
    update_[K, V, V, Maybe[V] |*| *](
      ins = id[V] >>> introFst >>> par(Maybe.empty[V], id),
      upd = swap[V, V] >>> par(Maybe.just[V], id),
    )

  /**
    *
    * @param update function used to update the current value under the given key, if any.
    *               The first argument of `update` is the new value, the second argument is
    *               the current value stored in the tree.
    */
  def insertOrUpdate[K: Ordering, V](
    update: (V |*| V) -⚬ V,
  ): ((Val[K] |*| V) |*| Tree[K, V]) -⚬ Tree[K, V] =
    update_[K, V, V, Id](
      ins = id[V],
      upd = update,
    )

  /** Witnesses that `F` is a functor such that `F[X]` has exactly one copy of `X`. */
  private trait Once[F[_]] extends CoFunctor[F] {
    def captureL[A, B]: (A |*| F[B]) -⚬ F[A |*| B]
    def releaseL[A, B]: F[A |*| B] -⚬ (A |*| F[B])
    def captureR[A, B]: (F[A] |*| B) -⚬ F[A |*| B]
    def releaseR[A, B]: F[A |*| B] -⚬ (F[A] |*| B)
  }

  private object Once {
    implicit def onceId[X]: Once[Id] =
      new Once[Id] {
        def lift[A, B](f: A -⚬ B): Id[A] -⚬ Id[B] = f
        def captureL[A, B]: (A |*| Id[B]) -⚬ Id[A |*| B] = id
        def captureR[A, B]: (Id[A] |*| B) -⚬ Id[A |*| B] = id
        def releaseL[A, B]: Id[A |*| B] -⚬ (A |*| Id[B]) = id
        def releaseR[A, B]: Id[A |*| B] -⚬ (Id[A] |*| B) = id
      }

    implicit def onceSnd[X]: Once[X |*| *] =
      new Once[X |*| *] {
        def lift[A, B](f: A -⚬ B): X |*| A -⚬ (X |*| B) = liftSnd(f)
        def captureL[A, B]: (A |*| (X |*| B)) -⚬ (X |*| (A |*| B)) = XI
        def captureR[A, B]: ((X |*| A) |*| B) -⚬ (X |*| (A |*| B)) = timesAssocLR
        def releaseL[A, B]: (X |*| (A |*| B)) -⚬ (A |*| (X |*| B)) = XI
        def releaseR[A, B]: (X |*| (A |*| B)) -⚬ ((X |*| A) |*| B) = timesAssocRL
      }
  }
}
