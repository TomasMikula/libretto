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

    def minKeyGetter[K]: Getter[Summary[K], Val[K]]
    def maxKeyGetter[K]: Getter[Summary[K], Val[K]]

    def dup[K]: Summary[K] -⚬ (Summary[K] |*| Summary[K])
    def discard[K]: Summary[K] -⚬ One
    def neglect[K]: Summary[K] -⚬ Done

    implicit def summaryComonoid[K]: Comonoid[Summary[K]]
  }

  val Summary: SummaryModule = new SummaryModule {
    //                minKey |*| maxKey
    type Summary[K] = Val[K] |*| Val[K]

    def singleton[K]: Val[K] -⚬ Summary[K] =
      dsl.dup

    def minKey[K]: Summary[K] -⚬ Val[K] =
      unliftPair >>> liftV(_._1)

    def maxKey[K]: Summary[K] -⚬ Val[K] =
      unliftPair >>> liftV(_._2)

    def minKeyGetter[K]: Getter[Summary[K], Val[K]] =
      fst[Val[K]].lens[Val[K]]

    def maxKeyGetter[K]: Getter[Summary[K], Val[K]] =
      snd[Val[K]].lens[Val[K]]

    def merge[K]: (Summary[K] |*| Summary[K]) -⚬ Summary[K] =
      par(minKey, maxKey)

    def dup[K]: Summary[K] -⚬ (Summary[K] |*| Summary[K]) =
      par(dsl.dup[K], dsl.dup[K]) >>> IXI

    def discard[K]: Summary[K] -⚬ One =
      parToOne(dsl.discard, dsl.discard)

    def neglect[K]: Summary[K] -⚬ Done =
      discard >>> done

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
    def summary[K, V]: Getter[Singleton[K, V], Summary[K]]
    def clear[K, V](f: V -⚬ One): Singleton[K, V] -⚬ One

    def keyGetter[K, V]: Getter[Singleton[K, V], Val[K]]
  }

  val Singleton: SingletonModule = new SingletonModule {
    type Singleton[K, V] = Val[K] |*| V

    def of[K, V]: (Val[K] |*| V) -⚬ Singleton[K, V] =
      id

    def deconstruct[K, V]: Singleton[K, V] -⚬ (Val[K] |*| V) =
      id

    def key[K, V]: Singleton[K, V] -⚬ (Val[K] |*| Singleton[K, V]) =
      getFst(lib.comonoidVal)

    def summary[K, V]: Getter[Singleton[K, V], Summary[K]] = {
      val singletonSummary: Getter[Val[K], Summary[K]] =
        new Getter[Val[K], Summary[K]] {
          override def getL[B](that: Getter[Summary[K], B])(implicit B: Cosemigroup[B]): Val[K] -⚬ (B |*| Val[K]) =
            (Summary.singleton[K] >>> that.getL).in.snd(Summary.minKey)

          override def extendJunction(j: Junction[Summary[K]]): Junction[Val[K]] =
            Junction.junctionVal[K]
        }

      singletonSummary compose fst[V].lens
    }

    def clear[K, V](f: V -⚬ One): Singleton[K, V] -⚬ One =
      parToOne(dsl.discard, f)

    def keyGetter[K, V]: Getter[Singleton[K, V], Val[K]] = lib.fst[V].lens[Val[K]]
  }

  import Singleton.Singleton

  sealed trait BranchFModule {
    type BranchF[K, X]

    def of[K, X](summary: Getter[X, Summary[K]]): (X |*| X) -⚬ BranchF[K, X]
    def deconstruct[K, X](j: Junction[X]): BranchF[K, X] -⚬ (X |*| X)
    def clear[K, X](f: X -⚬ One): BranchF[K, X] -⚬ One

    def summary[K, X]: Getter[BranchF[K, X], Summary[K]]
    def minKey[K, X]: Getter[BranchF[K, X], Val[K]]
    def maxKey[K, X]: Getter[BranchF[K, X], Val[K]]
  }

  val BranchF: BranchFModule = new BranchFModule {
    type BranchF[K, X] = Summary[K] |*| (X |*| X)

    def of[K, X](summary: Getter[X, Summary[K]]): (X |*| X) -⚬ BranchF[K, X] =
      id                                     [                 X  |*|                 X  ]
        .par(summary.getL, summary.getL)  .to[ (Summary[K] |*| X) |*| (Summary[K] |*| X) ]
        .andThen(IXI)                     .to[ (Summary[K] |*| Summary[K]) |*| (X |*| X) ]
        .in.fst(Summary.merge)            .to[         Summary[K]          |*| (X |*| X) ]

    def deconstruct[K, X](j: Junction[X]): BranchF[K, X] -⚬ (X |*| X) =
      id[BranchF[K, X]]                 .to[ Summary[K] |*| (X |*| X) ]
        .in.fst(Summary.neglect)        .to[    Done    |*| (X |*| X) ]
        .andThen(fst[X].lens.joinL(j))  .to[                 X |*| X  ]

    def clear[K, X](f: X -⚬ One): BranchF[K, X] -⚬ One =
      parToOne(Summary.discard, parToOne(f, f))

    def summary[K, X]: Getter[BranchF[K, X], Summary[K]] =
      fst[X |*| X].lens[Summary[K]]

    def minKey[K, X]: Getter[BranchF[K, X], Val[K]] =
      summary andThen Summary.minKeyGetter

    def maxKey[K, X]: Getter[BranchF[K, X], Val[K]] =
      summary andThen Summary.maxKeyGetter
  }

  import BranchF.BranchF

  type NonEmptyTreeF[K, V, X] = Singleton[K, V] |+| BranchF[K, X]
  type NonEmptyTree[K, V] = Rec[NonEmptyTreeF[K, V, *]]

  type Branch[K, V] = BranchF[K, NonEmptyTree[K, V]]

  object Branch {
    def apply[K, V]: (NonEmptyTree[K, V] |*| NonEmptyTree[K, V]) -⚬ Branch[K, V] =
      BranchF.of(NonEmptyTree.summary)

    def deconstruct[K, V]: Branch[K, V] -⚬ (NonEmptyTree[K, V] |*| NonEmptyTree[K, V]) =
      BranchF.deconstruct(NonEmptyTree.minKey[K, V].extendJunction(Junction.junctionVal[K]))

    def clear[K, V](subClear: NonEmptyTree[K, V] -⚬ One): Branch[K, V] -⚬ One =
      BranchF.clear(subClear)

    def summary[K, V]: Getter[Branch[K, V], Summary[K]] =
      BranchF.summary

    def minKey[K, V]: Getter[Branch[K, V], Val[K]] =
      BranchF.minKey

    def maxKey[K, V]: Getter[Branch[K, V], Val[K]] =
      BranchF.maxKey
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

    def summary[K, V]: Getter[NonEmptyTree[K, V], Summary[K]] =
      Lens.rec[NonEmptyTreeF[K, V, *]] andThen (Singleton.summary[K, V] |+| Branch.summary[K, V])

    def minKey[K, V]: Getter[NonEmptyTree[K, V], Val[K]] =
      Lens
        .rec[NonEmptyTreeF[K, V, *]]
        .andThen(Singleton.keyGetter[K, V] |+| Branch.minKey[K, V])

    def maxKey[K, V]: Getter[NonEmptyTree[K, V], Val[K]] =
      Lens
        .rec[NonEmptyTreeF[K, V, *]]
        .andThen(Singleton.keyGetter[K, V] |+| Branch.maxKey[K, V])

    private[BinarySearchTree] def update_[K: Ordering, V, W, F[_]](
      ins:         W -⚬ F[V],
      upd: (W |*| V) -⚬ F[V],
    )(implicit
      F: Absorptive[F],
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
      F: Absorptive[F],
    ): ((Val[K] |*| W) |*| Singleton[K, V]) -⚬ F[NonEmptyTree[K, V]] = {
      val intoR: ((Val[K] |*| W) |*| Singleton[K, V]) -⚬ F[NonEmptyTree[K, V]] =
        id                                                       [     (Val[K] |*| W) |*|    Singleton[K, V]    ]
          .swap                                               .to[    Singleton[K, V] |*|  (  Val[K] |*|   W  ) ]
          .in.snd.snd(ins)                                    .to[    Singleton[K, V] |*|  (  Val[K] |*| F[V] ) ]
          .in.snd(F.absorbOrDiscardL)                         .to[    Singleton[K, V] |*| F[  Val[K] |*|   V  ] ]
          .andThen(par(injectSingleton, F.lift(singleton)))   .to[ NonEmptyTree[K, V] |*| F[NonEmptyTree[K, V]] ]
          .andThen(F.absorbL(branch, id))                     .to[            F[NonEmptyTree[K, V]]             ]

      val intoL: ((Val[K] |*| W) |*| Singleton[K, V]) -⚬ F[NonEmptyTree[K, V]] =
        id                                                       [  (Val[K] |*|  W  )    |*|   Singleton[K, V]  ]
          .in.fst.snd(ins)                                    .to[  (Val[K] |*| F[V])    |*|   Singleton[K, V]  ]
          .in.fst(F.absorbOrDiscardL)                         .to[ F[Val[K] |*|   V ]    |*|   Singleton[K, V]  ]
          .andThen(par(F.lift(singleton), injectSingleton))   .to[ F[NonEmptyTree[K, V]] |*| NonEmptyTree[K, V] ]
          .andThen(F.absorbR(branch, id))                     .to[             F[NonEmptyTree[K, V]]            ]

      val replace: ((Val[K] |*| W) |*| Singleton[K, V]) -⚬ F[NonEmptyTree[K, V]] =
        id                                                       [ (Val[K] |*| W) |*| Singleton[K, V] ]
          .andThen(par(discardFst, Singleton.deconstruct))    .to[             W  |*|  (Val[K] |*| V) ]
          .andThen(XI)                                        .to[         Val[K] |*|       (W |*| V) ]
          .in.snd(upd)                                        .to[         Val[K] |*|            F[V] ]
          .andThen(F.absorbOrDiscardL)                        .to[       F[Val[K] |*|              V] ]
          .andThen(F.lift(singleton))                         .to[        F[NonEmptyTree[K, V]]       ]

      id                                                         [         (Val[K] |*| W) |*| Singleton[K, V]  ]
        .andThen(compareBy(fst[W].lens, Singleton.keyGetter)) .to[ Compared[Val[K] |*| W   ,  Singleton[K, V]] ]
        .andThen(compared(intoL, replace, intoR))             .to[          F[NonEmptyTree[K, V]]              ]
    }

    /** Update branch. */
    private def bUpdate[K: Ordering, V, W, F[_]](
      subUpdate: ((Val[K] |*| W) |*| NonEmptyTree[K, V]) -⚬ F[NonEmptyTree[K, V]],
    )(implicit
      F: Absorptive[F],
    ): ((Val[K] |*| W) |*| Branch[K, V]) -⚬ F[NonEmptyTree[K, V]] = {
      type Tree = NonEmptyTree[K, V]
      type Elem = Val[K] |*| W

      val updateL: ((Elem |*| Tree) |*| Tree) -⚬ F[Tree] =
        id                                   [ (Elem |*| Tree) |*| Tree  ]
          .in.fst(subUpdate)              .to[    F[Tree]      |*| Tree  ]
          .andThen(F.absorbR(branch, id)) .to[    F[          Tree     ] ]

      val updateR: (Tree |*| (Elem |*| Tree)) -⚬ F[Tree] =
        id                                   [   Tree |*| (Elem |*| Tree) ]
          .in.snd(subUpdate)              .to[   Tree |*|     F[Tree]     ]
          .andThen(F.absorbL(branch, id)) .to[ F[     Tree          ]     ]

      id                                     [                  Elem |*|         Branch[K, V]            ]
        .in.snd(Branch.deconstruct)       .to[                  Elem |*| (Tree                 |*| Tree) ]
        .timesAssocRL                     .to[                 (Elem |*| Tree)                 |*| Tree  ]
        .in.fst(sortBy(fst.lens, maxKey)) .to[ ((Elem |*| Tree)           |+| (Tree |*| Elem)) |*| Tree  ]
        .distributeRL                     .to[ ((Elem |*| Tree) |*| Tree) |+| ((Tree |*| Elem) |*| Tree) ]
        .in.right(timesAssocLR)           .to[ ((Elem |*| Tree) |*| Tree) |+| (Tree |*| (Elem |*| Tree)) ]
        .either(updateL, updateR)         .to[                          F[Tree]                          ]
    }

    def update[K: Ordering, V, A](
      f: A |*| V -⚬ Maybe[V],
    ): (Val[K] |*| A) |*| NonEmptyTree[K, V] -⚬ (Maybe[A] |*| Maybe[NonEmptyTree[K, V]]) =
      update_[K, V, A, BiMaybe[A, *]](
        ins = Maybe.just[A] >>> introSnd(Maybe.empty[V]),
        upd = f >>> introFst(Maybe.empty[A]),
      )

    def clear[K, V](f: V -⚬ One): NonEmptyTree[K, V] -⚬ One =
      rec { self =>
        unpack[NonEmptyTreeF[K, V, *]] >>> either(Singleton.clear(f), Branch.clear(self))
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
    F: Absorptive[F],
  ): ((Val[K] |*| W) |*| Tree[K, V]) -⚬ F[Tree[K, V]] = {
    val NET = NonEmptyTree
    type NET[K, V] = NonEmptyTree[K, V]

    id[(Val[K] |*| W) |*| Tree[K, V]]   .to[          (Val[K] |*| W) |*| (One |+| NET[K, V])                ]
      .distributeLR                     .to[ ((Val[K] |*|  W  ) |*| One) |+| ((Val[K] |*| W) |*| NET[K, V]) ]
      .in.right(NET.update_(ins, upd))  .to[ ((Val[K] |*|  W  ) |*| One) |+|           F[ NET[K, V]]        ]
      .in.right.co[F].injectR[One]      .to[ ((Val[K] |*|  W  ) |*| One) |+|           F[Tree[K, V]]        ]
      .in.left(elimSnd)                 .to[  (Val[K] |*|  W  )          |+|           F[Tree[K, V]]        ]
      .in.left.snd(ins)                 .to[  (Val[K] |*| F[V])          |+|           F[Tree[K, V]]        ]
      .in.left(F.absorbOrDiscardL)      .to[   F[Val[K] |*| V]           |+|           F[Tree[K, V]]        ]
      .in.left(F.lift(singleton))       .to[   F[ Tree[K, V] ]           |+|           F[Tree[K, V]]        ]
      .andThen(either(id, id))          .to[                        F[Tree[K, V]]                           ]
  }

  def insert[K: Ordering, V]: ((Val[K] |*| V) |*| Tree[K, V]) -⚬ (Maybe[V] |*| Tree[K, V]) =
    update_[K, V, V, Maybe[V] |*| *](
      ins = id[V].introFst(Maybe.empty[V]),
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

  private type BiMaybe[A, B] = Maybe[A] |*| Maybe[B]

  def delete[K: Ordering, V]: (Val[K] |*| Tree[K, V]) -⚬ (Maybe[V] |*| Tree[K, V]) = {
    val go: ((Val[K] |*| One) |*| Tree[K, V]) -⚬ BiMaybe[V, Tree[K, V]] =
      update_[K, V, One, BiMaybe[V, *]](
        ins = parFromOne(Maybe.empty[V], Maybe.empty[V]),
        upd = swap[One, V] >>> par(Maybe.just, Maybe.empty)
      )

    id                                           [  Val[K]          |*| Tree[K, V] ]
      .in.fst(introSnd)                       .to[ (Val[K] |*| One) |*| Tree[K, V] ]
      .andThen(go)                            .to[ Maybe[V] |*| Maybe[Tree[K, V]]  ]
      .in.snd(Maybe.getOrElse(empty[K, V]))   .to[ Maybe[V] |*|       Tree[K, V]   ]
  }

  def update[K: Ordering, V, A](
    f: A |*| V -⚬ Maybe[V],
  ): (Val[K] |*| A) |*| Tree[K, V] -⚬ (Maybe[A] |*| Tree[K, V]) =
    update_[K, V, A, BiMaybe[A, *]](
      ins = Maybe.just[A] >>> introSnd(Maybe.empty[V]),
      upd = f >>> introFst(Maybe.empty[A]),
    )
      .in.snd(Maybe.getOrElse(empty[K, V]))

  def clear[K, V](f: V -⚬ One): Tree[K, V] -⚬ One =
    either(id, NonEmptyTree.clear(f))

  private trait Absorptive[F[_]] extends Functor[F] { F =>
    def absorbOrDiscardL[A: Comonoid, B]: (A |*| F[B]) -⚬ F[A |*| B]
    def absorbL[A, B, C](combine: (A |*| B) -⚬ C, recover: A -⚬ C): (A |*| F[B]) -⚬ F[C]

    def absorbOrDiscardR[A, B: Comonoid]: (F[A] |*| B) -⚬ F[A |*| B] =
      swap >>> absorbOrDiscardL[B, A] >>> lift(swap)

    def absorbR[A, B, C](combine: (A |*| B) -⚬ C, recover: B -⚬ C): (F[A] |*| B) -⚬ F[C] =
      swap >>> absorbL(swap >>> combine, recover)

    def absorbL[A, B]: (A |*| F[B]) -⚬ F[A |*| Maybe[B]] =
      absorbL(par(id, Maybe.just), introSnd(Maybe.empty))

    def absorbR[A, B]: (F[A] |*| B) -⚬ F[Maybe[A] |*| B] =
      absorbR(par(Maybe.just, id), introFst(Maybe.empty))

    def >>>[G[_]](implicit G: Transportive[G]): Absorptive[λ[x => G[F[x]]]] =
      new Absorptive[λ[x => G[F[x]]]] {
        override def lift[A, B](f: A -⚬ B): G[F[A]] -⚬ G[F[B]] =
          G.lift(F.lift(f))

        override def absorbOrDiscardL[A, B](implicit A: Comonoid[A]): A |*| G[F[B]] -⚬ G[F[A |*| B]] =
          G.inL >>> G.lift(F.absorbOrDiscardL)

        override def absorbOrDiscardR[A, B](implicit B: Comonoid[B]): G[F[A]] |*| B -⚬ G[F[A |*| B]] =
          G.inR >>> G.lift(F.absorbOrDiscardR)

        override def absorbL[A, B, C](combine: A |*| B -⚬ C, recover: A -⚬ C): A |*| G[F[B]] -⚬ G[F[C]] =
          G.inL >>> G.lift(F.absorbL(combine, recover))

        override def absorbR[A, B, C](combine: A |*| B -⚬ C, recover: B -⚬ C): G[F[A]] |*| B -⚬ G[F[C]] =
          G.inR >>> G.lift(F.absorbR(combine, recover))
      }
  }

  private object Absorptive {
    implicit def fromTransportive[F[_]](implicit F: Transportive[F]): Absorptive[F] =
      new Absorptive[F] {
        override def lift[A, B](f: A -⚬ B): F[A] -⚬ F[B] =
          F.lift(f)

        override def absorbOrDiscardL[A, B](implicit A: Comonoid[A]): A |*| F[B] -⚬ F[A |*| B] =
          F.inL

        override def absorbOrDiscardR[A, B](implicit B: Comonoid[B]): F[A] |*| B -⚬ F[A |*| B] =
          F.inR

        override def absorbL[A, B, C](combine: A |*| B -⚬ C, recover: A -⚬ C): A |*| F[B] -⚬ F[C] =
          F.inL >>> F.lift(combine)

        override def absorbR[A, B, C](combine: A |*| B -⚬ C, recover: B -⚬ C): F[A] |*| B -⚬ F[C] =
          F.inR >>> F.lift(combine)
      }

    implicit val absorptiveMaybe: Absorptive[Maybe] =
      new Absorptive[Maybe] {
        def lift[A, B](f: A -⚬ B): Maybe[A] -⚬ Maybe[B] =
          Bifunctor[|+|].lift(id, f)

        def absorbL[A, B, C](combine: A |*| B -⚬ C, recover: A -⚬ C): A |*| Maybe[B] -⚬ Maybe[C] =
          id[A |*| Maybe[B]]                      .to[ A |*| (One  |+|        B) ]
            .distributeLR                         .to[ (A |*| One) |+| (A |*| B) ]
            .in.left(elimSnd)                     .to[  A          |+| (A |*| B) ]
            .either(recover, combine)             .to[              C            ]
            .injectR                              .to[        Maybe[C]           ]

        def absorbOrDiscardL[A, B](implicit A: Comonoid[A]): A |*| Maybe[B] -⚬ Maybe[A |*| B] =
          id[A |*| Maybe[B]]                      .to[ A |*| (One  |+|        B) ]
            .distributeLR                         .to[ (A |*| One) |+| (A |*| B) ]
            .in.left(elimSnd >>> A.counit)        .to[    One      |+| (A |*| B) ]
      }

    implicit def absorptiveBiMaybe[X]: Absorptive[BiMaybe[X, *]] =
      absorptiveMaybe >>> snd
  }
}
