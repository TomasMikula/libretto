package libretto

object BinarySearchTree {
  def apply(
    dsl: ScalaDSL,
    coreLib: CoreLib[dsl.type],
    scalaLib: ScalaLib[dsl.type, coreLib.type],
  )
  : BinarySearchTree[dsl.type, coreLib.type, scalaLib.type] =
    new BinarySearchTree(dsl, coreLib, scalaLib)
}

class BinarySearchTree[DSL <: ScalaDSL, CLib <: CoreLib[DSL], SLib <: ScalaLib[DSL, CLib]](
  val dsl: DSL,
  val coreLib: CLib with CoreLib[dsl.type],
  val scalaLib: SLib with ScalaLib[dsl.type, coreLib.type],
) {
  import dsl._
  import coreLib._
  import coreLib.Bool._
  import coreLib.Compared._
  import scalaLib._

  object Summary {
    //                       minKey |*| maxKey
    opaque type Summary[K] = Val[K] |*| Val[K]

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

    def neglect[K]: Summary[K] -⚬ Done =
      join(dsl.neglect, dsl.neglect)

    implicit def summaryCosemigroup[K]: Cosemigroup[Summary[K]] =
      new Cosemigroup[Summary[K]] {
        def split : Summary[K] -⚬ (Summary[K] |*| Summary[K]) = dup
      }
  }

  import Summary.{Summary, summaryCosemigroup}

  object Singleton {
    opaque type Singleton[K, V] = Val[K] |*| V

    def of[K, V]: (Val[K] |*| V) -⚬ Singleton[K, V] =
      id

    def deconstruct[K, V]: Singleton[K, V] -⚬ (Val[K] |*| V) =
      id

    def key[K, V]: Singleton[K, V] -⚬ (Val[K] |*| Singleton[K, V]) =
      getFst(scalaLib.pComonoidVal)

    def summary[K, V]: Getter[Singleton[K, V], Summary[K]] = {
      val singletonSummary: Getter[Val[K], Summary[K]] =
        new Getter[Val[K], Summary[K]] {
          override def getL[B](that: Getter[Summary[K], B])(implicit B: Cosemigroup[B]): Val[K] -⚬ (B |*| Val[K]) =
            (Summary.singleton[K] >>> that.getL).in.snd(Summary.minKey)

          override def extendJunction(implicit j: Junction.Positive[Summary[K]]): Junction.Positive[Val[K]] =
            scalaLib.junctionVal[K]
        }

      singletonSummary compose fst[V].lens
    }

    def clear[K, V](f: V -⚬ Done): Singleton[K, V] -⚬ Done =
      join(dsl.neglect, f)

    def keyGetter[K, V]: Getter[Singleton[K, V], Val[K]] = coreLib.fst[V].lens[Val[K]]

    def keyJoinL[K, V]: (Done |*| Singleton[K, V]) -⚬ Singleton[K, V] =
      keyGetter[K, V].extendJunction.awaitPosFst

    def keyJoinR[K, V]: (Singleton[K, V] |*| Done) -⚬ Singleton[K, V] =
      keyGetter[K, V].extendJunction.awaitPosSnd
  }

  import Singleton.Singleton

  object BranchF {
    opaque type BranchF[K, X] = Summary[K] |*| (X |*| X)

    def of[K, X](summary: Getter[X, Summary[K]]): (X |*| X) -⚬ BranchF[K, X] =
      id                                     [                 X  |*|                 X  ]
        .par(summary.getL, summary.getL)  .to[ (Summary[K] |*| X) |*| (Summary[K] |*| X) ]
        .andThen(IXI)                     .to[ (Summary[K] |*| Summary[K]) |*| (X |*| X) ]
        .in.fst(Summary.merge)            .to[         Summary[K]          |*| (X |*| X) ]

    def deconstruct[K, X](j: Junction.Positive[X]): BranchF[K, X] -⚬ (X |*| X) =
      id[BranchF[K, X]]                 .to[ Summary[K] |*| (X |*| X) ]
        .in.fst(Summary.neglect)        .to[    Done    |*| (X |*| X) ]
        .andThen(fst[X].lens.joinL(j))  .to[                 X |*| X  ]

    def clear[K, X](f: X -⚬ Done): BranchF[K, X] -⚬ Done =
      join(Summary.neglect, join(f, f))

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
      BranchF.deconstruct(NonEmptyTree.minKey[K, V].extendJunction(scalaLib.junctionVal[K]))

    def clear[K, V](subClear: NonEmptyTree[K, V] -⚬ Done): Branch[K, V] -⚬ Done =
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

    private def minKeyJoinL[K, V]: (Done |*| NonEmptyTree[K, V]) -⚬ NonEmptyTree[K, V] =
      minKey[K, V].extendJunction.awaitPosFst

    private def maxKeyJoinR[K, V]: (NonEmptyTree[K, V] |*| Done) -⚬ NonEmptyTree[K, V] =
      maxKey[K, V].extendJunction.awaitPosSnd

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
      val intoR: ((Val[K] |*| W) |*| Singleton[K, V]) -⚬ F[NonEmptyTree[K, V]] = {
        val absorbSingleton: (Singleton[K, V] |*| F[NonEmptyTree[K, V]]) -⚬ F[NonEmptyTree[K, V]] =
          F.absorbL(par(injectSingleton[K, V], id[NonEmptyTree[K, V]]) >>> branch, Singleton.keyJoinR >>> injectSingleton)

        id                                                       [     (Val[K] |*| W) |*|    Singleton[K, V]    ]
          .swap                                               .to[    Singleton[K, V] |*|  (  Val[K] |*|   W  ) ]
          .in.snd.snd(ins)                                    .to[    Singleton[K, V] |*|  (  Val[K] |*| F[V] ) ]
          .in.snd(F.absorbOrNeglectL)                         .to[    Singleton[K, V] |*| F[  Val[K] |*|   V  ] ]
          .in.snd(F.lift(singleton))                          .to[    Singleton[K, V] |*| F[NonEmptyTree[K, V]] ]
          .andThen(absorbSingleton)                           .to[            F[NonEmptyTree[K, V]]             ]
      }

      val intoL: ((Val[K] |*| W) |*| Singleton[K, V]) -⚬ F[NonEmptyTree[K, V]] = {
        val absorbSingleton: (F[NonEmptyTree[K, V]] |*| Singleton[K, V]) -⚬ F[NonEmptyTree[K, V]] =
          F.absorbR(par(id[NonEmptyTree[K, V]], injectSingleton[K, V]) >>> branch, Singleton.keyJoinL >>> injectSingleton)

        id                                                       [  (Val[K] |*|  W     ) |*|   Singleton[K, V]  ]
          .in.fst.snd(ins)                                    .to[  (Val[K] |*| F[V]   ) |*|   Singleton[K, V]  ]
          .in.fst(F.absorbOrNeglectL)                         .to[ F[Val[K] |*|   V    ] |*|   Singleton[K, V]  ]
          .in.fst(F.lift(singleton))                          .to[ F[NonEmptyTree[K, V]] |*|   Singleton[K, V]  ]
          .andThen(absorbSingleton)                           .to[             F[NonEmptyTree[K, V]]            ]
      }

      val replace: ((Val[K] |*| W) |*| Singleton[K, V]) -⚬ F[NonEmptyTree[K, V]] =
        id                                                       [ (Val[K] |*| W) |*| Singleton[K, V] ]
          .in.snd(Singleton.deconstruct)                      .to[ (Val[K] |*| W) |*|  (Val[K] |*| V) ]
          .andThen(IXI).in.fst.joinL(neglect)                 .to[         Val[K] |*|       (W |*| V) ]
          .in.snd(upd)                                        .to[         Val[K] |*|            F[V] ]
          .andThen(F.absorbOrNeglectL)                        .to[       F[Val[K] |*|              V] ]
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
        id                                                 [ (Elem |*| Tree) |*| Tree  ]
          .in.fst(subUpdate)                            .to[    F[Tree]      |*| Tree  ]
          .andThen(F.absorbR(branch, minKeyJoinL))      .to[    F[          Tree     ] ]

      val updateR: (Tree |*| (Elem |*| Tree)) -⚬ F[Tree] =
        id                                                 [   Tree |*| (Elem |*| Tree) ]
          .in.snd(subUpdate)                            .to[   Tree |*|     F[Tree]     ]
          .andThen(F.absorbL(branch, maxKeyJoinR))      .to[ F[     Tree          ]     ]

      id                                     [                  Elem |*|         Branch[K, V]            ]
        .in.snd(Branch.deconstruct)       .to[                  Elem |*| (Tree                 |*| Tree) ]
        .assocRL                          .to[                 (Elem |*| Tree)                 |*| Tree  ]
        .in.fst(sortBy(fst.lens, maxKey)) .to[ ((Elem |*| Tree)           |+| (Tree |*| Elem)) |*| Tree  ]
        .distributeRL                     .to[ ((Elem |*| Tree) |*| Tree) |+| ((Tree |*| Elem) |*| Tree) ]
        .in.right.assocLR                 .to[ ((Elem |*| Tree) |*| Tree) |+| (Tree |*| (Elem |*| Tree)) ]
        .either(updateL, updateR)         .to[                          F[Tree]                          ]
    }

    def update[K: Ordering, V, A](
      f: (A |*| V) -⚬ PMaybe[V],
    ): ((Val[K] |*| A) |*| NonEmptyTree[K, V]) -⚬ (PMaybe[A] |*| PMaybe[NonEmptyTree[K, V]]) =
      update_[K, V, A, λ[x => PMaybe[A] |*| PMaybe[x]]](
        ins = PMaybe.just[A] >>> introSnd(done >>> PMaybe.empty[V]),
        upd = f >>> introFst(done >>> PMaybe.empty[A]),
      )

    def update[K: Ordering, V, A](
      f: (A |*| V) -⚬ PMaybe[V],
      ifAbsent: A -⚬ Done,
    ): ((Val[K] |*| A) |*| NonEmptyTree[K, V]) -⚬ PMaybe[NonEmptyTree[K, V]] =
      update_[K, V, A, PMaybe](
        ins = ifAbsent >>> PMaybe.empty[V],
        upd = f,
      )

    def clear[K, V](f: V -⚬ Done): NonEmptyTree[K, V] -⚬ Done =
      rec { self =>
        unpack[NonEmptyTreeF[K, V, *]] >>> either(Singleton.clear(f), Branch.clear(self))
      }
  }

  type Tree[K, V] = Done |+| NonEmptyTree[K, V]

  def empty[K, V]: Done -⚬ Tree[K, V] =
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

    id[(Val[K] |*| W) |*| Tree[K, V]]   .to[          (Val[K] |*| W) |*| (Done |+| NET[K, V])                ]
      .distributeLR                     .to[ ((Val[K] |*|  W  ) |*| Done) |+| ((Val[K] |*| W) |*| NET[K, V]) ]
      .in.right(NET.update_(ins, upd))  .to[ ((Val[K] |*|  W  ) |*| Done) |+|           F[ NET[K, V]]        ]
      .in.right.co[F].injectR[Done]     .to[ ((Val[K] |*|  W  ) |*| Done) |+|           F[Tree[K, V]]        ]
      .in.left(IX)                      .to[ ((Val[K] |*| Done) |*|  W  ) |+|           F[Tree[K, V]]        ]
      .in.left.fst.joinR                .to[ ( Val[K]           |*|  W  ) |+|           F[Tree[K, V]]        ]
      .in.left.snd(ins)                 .to[ ( Val[K]           |*| F[V]) |+|           F[Tree[K, V]]        ]
      .in.left(F.absorbOrNeglectL)      .to[ F[Val[K]           |*|  V  ] |+|           F[Tree[K, V]]        ]
      .in.left(F.lift(singleton))       .to[ F[            Tree[K, V]   ] |+|           F[Tree[K, V]]        ]
      .andThen(either(id, id))          .to[                         F[Tree[K, V]]                           ]
  }

  def insert[K: Ordering, V]: ((Val[K] |*| V) |*| Tree[K, V]) -⚬ (Maybe[V] |*| Tree[K, V]) =
    update_[K, V, V, λ[x => Maybe[V] |*| x]](
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

  def delete[K: Ordering, V]: (Val[K] |*| Tree[K, V]) -⚬ (Maybe[V] |*| Tree[K, V]) = {
    val go: ((Val[K] |*| One) |*| Tree[K, V]) -⚬ (Maybe[V] |*| PMaybe[Tree[K, V]]) =
      update_[K, V, One, λ[x => Maybe[V] |*| PMaybe[x]]](
        ins = parFromOne(Maybe.empty[V], done >>> PMaybe.empty[V]),
        upd = swap[One, V] >>> par(Maybe.just, done >>> PMaybe.empty)
      )

    id                                           [  Val[K]          |*| Tree[K, V] ]
      .in.fst(introSnd)                       .to[ (Val[K] |*| One) |*| Tree[K, V] ]
      .andThen(go)                            .to[ Maybe[V] |*| PMaybe[Tree[K, V]] ]
      .in.snd(PMaybe.getOrElse(empty[K, V]))  .to[ Maybe[V] |*|        Tree[K, V]  ]
  }

  def update[K: Ordering, V, A](
    f: (A |*| V) -⚬ PMaybe[V],
  ): ((Val[K] |*| A) |*| Tree[K, V]) -⚬ (PMaybe[A] |*| Tree[K, V]) =
    update_[K, V, A, λ[x => PMaybe[A] |*| PMaybe[x]]](
      ins = PMaybe.just[A] >>> introSnd(done >>> PMaybe.empty[V]),
      upd = f >>> introFst(done >>> PMaybe.empty[A]),
    )
      .in.snd(PMaybe.getOrElse(empty[K, V]))

  def update[K: Ordering, V, A](
    f: (A |*| V) -⚬ PMaybe[V],
    ifAbsent: A -⚬ Done,
  ): ((Val[K] |*| A) |*| Tree[K, V]) -⚬ Tree[K, V] =
    update_[K, V, A, PMaybe](
      ins = ifAbsent >>> PMaybe.empty[V],
      upd = f,
    )
      .andThen(PMaybe.getOrElse(empty[K, V]))

  def clear[K, V](f: V -⚬ Done): Tree[K, V] -⚬ Done =
    either(id, NonEmptyTree.clear(f))

  private trait Absorptive[F[_]] extends Functor[F] { F =>
    def absorbOrNeglectL[A: PComonoid, B]: (A |*| F[B]) -⚬ F[A |*| B]
    def absorbL[A, B, C](combine: (A |*| B) -⚬ C, recover: (A |*| Done) -⚬ C): (A |*| F[B]) -⚬ F[C]

    def absorbOrNeglectR[A, B: PComonoid]: (F[A] |*| B) -⚬ F[A |*| B] =
      swap >>> absorbOrNeglectL[B, A] >>> lift(swap)

    def absorbR[A, B, C](combine: (A |*| B) -⚬ C, recover: (Done |*| B) -⚬ C): (F[A] |*| B) -⚬ F[C] =
      swap >>> absorbL(swap >>> combine, swap >>> recover)

    def absorbL[A, B]: (A |*| F[B]) -⚬ F[A |*| PMaybe[B]] =
      absorbL(par(id, PMaybe.just), par(id, PMaybe.empty))

    def absorbR[A, B]: (F[A] |*| B) -⚬ F[PMaybe[A] |*| B] =
      absorbR(par(PMaybe.just, id), par(PMaybe.empty, id))

    def >>>[G[_]](implicit G: Transportive[G]): Absorptive[λ[x => G[F[x]]]] =
      new Absorptive[λ[x => G[F[x]]]] {
        override def lift[A, B](f: A -⚬ B): G[F[A]] -⚬ G[F[B]] =
          G.lift(F.lift(f))

        override def absorbOrNeglectL[A, B](implicit A: PComonoid[A]): (A |*| G[F[B]]) -⚬ G[F[A |*| B]] =
          G.inL >>> G.lift(F.absorbOrNeglectL)

        override def absorbOrNeglectR[A, B](implicit B: PComonoid[B]): (G[F[A]] |*| B) -⚬ G[F[A |*| B]] =
          G.inR >>> G.lift(F.absorbOrNeglectR)

        override def absorbL[A, B, C](combine: (A |*| B) -⚬ C, recover: (A |*| Done) -⚬ C): (A |*| G[F[B]]) -⚬ G[F[C]] =
          G.inL >>> G.lift(F.absorbL(combine, recover))

        override def absorbR[A, B, C](combine: (A |*| B) -⚬ C, recover: (Done |*| B) -⚬ C): (G[F[A]] |*| B) -⚬ G[F[C]] =
          G.inR >>> G.lift(F.absorbR(combine, recover))
      }
  }

  private object Absorptive {
    implicit def fromTransportive[F[_]](implicit F: Transportive[F]): Absorptive[F] =
      new Absorptive[F] {
        override def lift[A, B](f: A -⚬ B): F[A] -⚬ F[B] =
          F.lift(f)

        override def absorbOrNeglectL[A, B](implicit A: PComonoid[A]): (A |*| F[B]) -⚬ F[A |*| B] =
          F.inL

        override def absorbOrNeglectR[A, B](implicit B: PComonoid[B]): (F[A] |*| B) -⚬ F[A |*| B] =
          F.inR

        override def absorbL[A, B, C](combine: (A |*| B) -⚬ C, recover: (A |*| Done) -⚬ C): (A |*| F[B]) -⚬ F[C] =
          F.inL >>> F.lift(combine)

        override def absorbR[A, B, C](combine: (A |*| B) -⚬ C, recover: (Done |*| B) -⚬ C): (F[A] |*| B) -⚬ F[C] =
          F.inR >>> F.lift(combine)
      }

    implicit def insideTransportive[F[_], G[_]](implicit F: Transportive[F], G: Absorptive[G]): Absorptive[λ[x => F[G[x]]]] =
      G >>> F

    implicit val absorptivePMaybe: Absorptive[PMaybe] =
      new Absorptive[PMaybe] {
        override def lift[A, B](f: A -⚬ B): PMaybe[A] -⚬ PMaybe[B] =
          Bifunctor[|+|].lift(id, f)

        override def absorbL[A, B, C](combine: (A |*| B) -⚬ C, recover: (A |*| Done) -⚬ C): (A |*| PMaybe[B]) -⚬ PMaybe[C] =
          id[A |*| PMaybe[B]]                     .to[ A |*| (Done  |+|        B) ]
            .distributeLR                         .to[ (A |*| Done) |+| (A |*| B) ]
            .either(recover, combine)             .to[               C            ]
            .injectR                              .to[        PMaybe[C]           ]

        override def absorbOrNeglectL[A, B](implicit A: PComonoid[A]):( A |*| PMaybe[B]) -⚬ PMaybe[A |*| B] =
          id[A |*| PMaybe[B]]                     .to[ A |*|    (Done  |+|        B) ]
            .distributeLR                         .to[ (A    |*| Done) |+| (A |*| B) ]
            .in.left.fst(A.counit)                .to[ (Done |*| Done) |+| (A |*| B) ]
            .in.left(join)                        .to[      Done       |+| (A |*| B) ]
      }
  }
}
