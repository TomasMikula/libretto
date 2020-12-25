package libretto

object LLists {
  def apply(
    dsl: CoreDSL,
    lib: CoreLib[dsl.type],
  )
  : LLists[dsl.type, lib.type] =
    new LLists(dsl, lib)
}

class LLists[DSL <: CoreDSL, Lib <: CoreLib[DSL]](
  val dsl: DSL,
  val lib: Lib with CoreLib[dsl.type],
) {
  import dsl._
  import lib._

  type LListF[T, X] = One |+| (T |*| X)
  type LList[T] = Rec[LListF[T, *]]

  def nil[T]: One -⚬ LList[T] =
    id[One]
      .injectL[T |*| LList[T]]
      .pack

  def cons[T]: (T |*| LList[T]) -⚬ LList[T] =
    id[T |*| LList[T]]
      .injectR[One]
      .pack

  def uncons[T]: LList[T] -⚬ Maybe[T |*| LList[T]] =
    unpack[LListF[T, *]]

  def map[T, U](f: T -⚬ U): LList[T] -⚬ LList[U] =
    rec { self =>
      uncons[T]
        .either(nil[U], par(f, self) >>> cons)
    }

  def consMaybe[T]: (Maybe[T] |*| LList[T]) -⚬ LList[T] =
    id[Maybe[T] |*| LList[T]]             .to[ (One |+|                T) |*| LList[T] ]
      .distributeRL                       .to[ (One |*| LList[T]) |+| (T |*| LList[T]) ]
      .andThen(either(elimFst, cons))     .to[                 LList[T]                ]

  def collect[T, U](f: T -⚬ Maybe[U]): LList[T] -⚬ LList[U] =
    rec { self =>
      uncons[T]
        .either(nil[U], par(f, self) >>> consMaybe)
    }

  def transform[T, A, U](f: (A |*| T) -⚬ U)(implicit A: Comonoid[A]): (A |*| LList[T]) -⚬ LList[U] =
    rec { self =>
      id                                   [  A |*|      LList[T]                             ]
        .in.snd(uncons)                 .to[  A |*| (One |+|                (T |*| LList[T])) ]
        .distributeLR                   .to[ (A |*| One) |+| (    A     |*| (T |*| LList[T])) ]
        .in.left(discardFst)            .to[        One  |+| (    A     |*| (T |*| LList[T])) ]
        .in.right.fst(A.split)          .to[        One  |+| ((A |*| A) |*| (T |*| LList[T])) ]
        .in.right(IXI)                  .to[        One  |+| ((A |*| T) |*| (A |*| LList[T])) ]
        .in.right(par(f, self))         .to[        One  |+| (    U     |*|    LList[U]     ) ]
        .either(nil[U], cons[U])        .to[            LList[U]                              ]
    }

  def transformCollect[T, A, U](f: (A |*| T) -⚬ Maybe[U])(implicit A: Comonoid[A]): (A |*| LList[T]) -⚬ LList[U] =
    rec { self =>
      id                                   [  A |*|      LList[T]                             ]
        .in.snd(uncons)                 .to[  A |*| (One |+|                (T |*| LList[T])) ]
        .distributeLR                   .to[ (A |*| One) |+| (    A     |*| (T |*| LList[T])) ]
        .in.left(discardFst)            .to[        One  |+| (    A     |*| (T |*| LList[T])) ]
        .in.right.fst(A.split)          .to[        One  |+| ((A |*| A) |*| (T |*| LList[T])) ]
        .in.right(IXI)                  .to[        One  |+| ((A |*| T) |*| (A |*| LList[T])) ]
        .in.right(par(f, self))         .to[        One  |+| ( Maybe[U] |*|    LList[U]     ) ]
        .either(nil[U], consMaybe[U])   .to[            LList[U]                              ]
    }
}
