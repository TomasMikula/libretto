package libretto.typology.toylang.typeinfer

import libretto.lambda.util.Monad.syntax._
import libretto.scaletto.StarterKit._
import libretto.testing.scalatest.scaletto.ScalatestStarterTestSuite
import libretto.testing.scaletto.StarterTestKit
import libretto.testing.TestCase
import libretto.typology.kinds._
import libretto.typology.toylang.typeinfer.TypeInference.inferTypes
import libretto.typology.toylang.terms.{Fun, TypedFun}
import libretto.typology.toylang.terms.Fun._
import libretto.typology.toylang.types._
import scala.concurrent.duration.*

class TypeInferenceTests extends ScalatestStarterTestSuite {
  type Type          = libretto.typology.toylang.types.Type[AbstractTypeLabel]
  type TypeFun[K, L] = libretto.typology.toylang.types.TypeFun[AbstractTypeLabel, K, L]
  type TypeTagF      = libretto.typology.toylang.types.TypeFun[ScalaTypeParam, ●, ●]

  def eitherBimap[A, B, C, D](f: Fun[A, C], g: Fun[B, D]): Fun[Either[A, B], Either[C, D]] =
    Fun.either(
      f > Fun.injectL,
      g > Fun.injectR,
    )

  type InfiniteList[A] = Fix[(A, _)]
  object InfiniteList {
    def tpe(elemType: Type): Type =
      Type.fix(TypeFun.pair1(elemType))

    def fix[A](using TypeTag[A]): Fun[(A, InfiniteList[A]), InfiniteList[A]] =
      Fun.fix[(A, _)]

    def unfix[A](using TypeTag[A]): Fun[InfiniteList[A], (A, InfiniteList[A])] =
      Fun.unfix[(A, _)]

    def fix_[A]: Fun[(A, InfiniteList[A]), InfiniteList[A]] =
      fix[A](using TypeTag.ofTypeParam[A])

    def unfix_[A]: Fun[InfiniteList[A], (A, InfiniteList[A])] =
      unfix[A](using TypeTag.ofTypeParam[A])

    def sum: Fun[InfiniteList[Int], Int] =
      Fun.rec(Fun.snd(unfix[Int] > Fun.swap) > Fun.assocRL > Fun.fst(Fun.recur) > Fun.addInts)

    def map[A, B](f: Fun[A, B])(using TypeTag[A], TypeTag[B]): Fun[InfiniteList[A], InfiniteList[B]] =
      Fun.recFun { map =>
        as => {
          val h <*> t = unfix[A](as)
          fix[B](f(h) <*> map(t))
        }
      }

    def map_[A, B](f: Fun[A, B]): Fun[InfiniteList[A], InfiniteList[B]] =
      map(f)(using TypeTag.ofTypeParam[A], TypeTag.ofTypeParam[B])
  }

  type ListF[A, X] = Either[Unit, (A, X)]
  object ListF {
    given typeTag: TypeTag[ListF] =
      TypeTag.compose2(TypeTag[Either[Unit, *]], TypeTag.pair)

    given typeTag[A](using TypeTag[A]): TypeTag[ListF[A, *]] =
      TypeTag.compose(TypeTag[Either[Unit, *]], TypeTag[(A, *)])
  }

  type List[A] = Fix[ListF[A, *]]
  object List {
    given TypeTag[List] =
      TypeTag.pfix[ListF](using ListF.typeTag)

    def tpe: TypeTagF =
      TypeTag.toTypeFun[List](summon[TypeTag[List]])

    def tag[A](using TypeTag[A]): TypeTag[List[A]] =
      TypeTag.app(TypeTag[List], TypeTag[A])

    def map[A, B](f: Fun[A, B])(using TypeTag[A], TypeTag[B]): Fun[List[A], List[B]] =
      Fun.recFun { map =>
        as =>
          val bs =
            Fun.unfix[ListF[A, *]](using ListF.typeTag[A])(as) switch {
              case Left(unit) =>
                Fun.injectL[Unit, (B, List[B])](unit)
              case Right(a <*> as) =>
                Fun.injectR[Unit, (B, List[B])](f(a) <*> map(as))
            }
          Fun.fix[ListF[B, *]](using ListF.typeTag[B])(bs)
      }

    def map_[A, B](f: Fun[A, B]): Fun[List[A], List[B]] = {
      given TypeTag[A] = TypeTag.ofTypeParam[A]
      given TypeTag[B] = TypeTag.ofTypeParam[B]
      map(f)
    }
  }

  type NonEmptyTreeF[A, X] = Either[A, (X, X)]
  object NonEmptyTreeF {
    given typeTag: TypeTag[NonEmptyTreeF] =
      TypeTag.composeSnd(TypeTag.sum, TypeTag.diag)

    given typeTag[A](using a: TypeTag[A]): TypeTag[NonEmptyTreeF[A, *]] =
      TypeTag.appFst(typeTag, a)
  }

  type NonEmptyTree[A] = Fix[NonEmptyTreeF[A, *]]
  object NonEmptyTree {
    given typeTag: TypeTag[NonEmptyTree] =
      TypeTag.pfix[NonEmptyTreeF](using NonEmptyTreeF.typeTag)

    def tpe: TypeTagF =
      TypeTag.toTypeFun(typeTag)

    def map_[A, B](f: Fun[A, B])(using TypeTag[A], TypeTag[B]): Fun[NonEmptyTree[A], NonEmptyTree[B]] = {
      Fun.rec(fun { case map <*> as =>
        val bs =
          Fun.unfix[NonEmptyTreeF[A, *]](using NonEmptyTreeF.typeTag[A])(as) switch {
            case Left(a) =>
              Fun.injectL(f(a))
            case Right(l <*> r) =>
              Fun.injectR(map(l) <*> map(r))
          }
        Fun.fix[NonEmptyTreeF[B, *]](using NonEmptyTreeF.typeTag[B])(bs)
      })
    }

    def map[A, B](f: Fun[A, B]): Fun[NonEmptyTree[A], NonEmptyTree[B]] = {
      given TypeTag[A] = TypeTag.ofTypeParam[A]
      given TypeTag[B] = TypeTag.ofTypeParam[B]

      map_[A, B](f)
    }
  }

  type Tree[A] = Either[Unit, NonEmptyTree[A]]
  object Tree {
    given typeTag: TypeTag[Tree] =
      TypeTag.compose(
        TypeTag.sum1[Unit],
        NonEmptyTree.typeTag,
      )

    def tpe: TypeTagF =
      TypeTag.toTypeFun[Tree](typeTag)

    def map[A, B](f: Fun[A, B]): Fun[Tree[A], Tree[B]] = {
      Fun.either(
        Fun.injectL[Unit, NonEmptyTree[B]],
        NonEmptyTree.map(f) > Fun.injectR[Unit, NonEmptyTree[B]],
      )
    }
  }

  trait Bifunctor[F[_, _]] {
    def lmap[A, B, C](f: Fun[A, C]): Fun[F[A, B], F[C, B]]
    def rmap[A, B, D](g: Fun[B, D]): Fun[F[A, B], F[A, D]]

    def bimap[A, B, C, D](f: Fun[A, C], g: Fun[B, D]): Fun[F[A, B], F[C, D]] =
      lmap(f) > rmap(g)
  }

  object Bifunctor {
    given Bifunctor[Tuple2] with {
      override def lmap[A, B, C](f: Fun[A, C]): Fun[(A, B), (C, B)] =
        Fun.par(f, Fun.id[B])

      override def rmap[A, B, D](g: Fun[B, D]): Fun[(A, B), (A, D)] =
        Fun.par(Fun.id[A], g)
    }
  }

  type Const[A, B] = A
  object Const {
    given bifunctorConst: Bifunctor[Const] with {
      override def lmap[A, B, C](f: Fun[A, C]): Fun[Const[A, B], Const[C, B]] =
        f

      override def rmap[A, B, D](g: Fun[B, D]): Fun[Const[A, B], Const[A, D]] =
        Fun.id[A]
    }
  }

  type Swap[F[_, _], A, B] = F[B, A]
  object Swap {
    given bifunctorSwap[F[_, _]](using F: Bifunctor[F]): Bifunctor[Swap[F, *, *]] with {
      override def lmap[A, B, C](f: Fun[A, C]): Fun[Swap[F, A, B], Swap[F, C, B]] =
        F.rmap(f)

      override def rmap[A, B, D](g: Fun[B, D]): Fun[Swap[F, A, B], Swap[F, A, D]] =
        F.lmap(g)
    }
  }

  override def testCases(using kit: StarterTestKit): scala.List[(String, TestCase[kit.type])] = {
    import kit.{Outcome, expectVal}
    import Outcome.assertEquals

    def testInferredTypes[A, B](f: Fun[A, B])(check: TypedFun[A, B] => Outcome[Unit]): TestCase.Single[kit.type] =
      TestCase
        .interactWith { λ { start => constant(inferTypes(f)) waitFor start } }
        .via { expectVal(_).flatMap(check) }

    scala.List(
      "infer types of id > intToString > id" ->
        testInferredTypes(Fun.id > Fun.intToString > Fun.id) { tf =>
          for {
            _ <- Outcome.assertEquals(tf.inType, Type.int)
            _ <- Outcome.assertEquals(tf.outType, Type.string)
          } yield ()
        },

      "infer types of swap > par(intToString, intToString) > swap" ->
        testInferredTypes(Fun.swap > Fun.par(Fun.intToString, Fun.intToString) > Fun.swap) { tf =>
          for {
            _ <- Outcome.assertEquals(tf.inType, Type.pair(Type.int, Type.int))
            _ <- Outcome.assertEquals(tf.outType, Type.pair(Type.string, Type.string))
          } yield ()
        },

      "infer types of adding ints ((a + b) + c) + d" ->
        testInferredTypes(Fun.fst(Fun.fst(Fun.addInts) > Fun.addInts) > Fun.addInts) { tf =>
          for {
            _ <- Outcome.assertEquals(tf.inType, Type.pair(Type.pair(Type.pair(Type.int, Type.int), Type.int), Type.int))
            _ <- Outcome.assertEquals(tf.outType, Type.int)
          } yield ()
        },

      "infer types of eitherBimap(intToString, intToString)" ->
        testInferredTypes(eitherBimap(Fun.intToString, Fun.intToString)) { tf =>
          for {
            _ <- Outcome.assertEquals(tf.inType, Type.sum(Type.int, Type.int))
            _ <- Outcome.assertEquals(tf.outType, Type.sum(Type.string, Type.string))
          } yield ()
        },

      "infer types of InfiniteList.fix[Int]" ->
        testInferredTypes(InfiniteList.fix[Int]) { tf =>
          for {
            _ <- Outcome.assertEquals(tf.inType, Type.pair(Type.int, InfiniteList.tpe(Type.int)))
            _ <- Outcome.assertEquals(tf.outType, InfiniteList.tpe(Type.int))
          } yield ()
        },

      "infer types of InfiniteList.unfix[Int]" ->
        testInferredTypes(InfiniteList.unfix[Int]) { tf =>
          for {
            _ <- Outcome.assertEquals(tf.inType, InfiniteList.tpe(Type.int))
            _ <- Outcome.assertEquals(tf.outType, Type.pair(Type.int, InfiniteList.tpe(Type.int)))
          } yield ()
        },

      "infer types of InfiniteList.unfix[Int] > swap" ->
        testInferredTypes(InfiniteList.unfix[Int] > Fun.swap) { tf =>
          for {
            _ <- Outcome.assertEquals(tf.inType, InfiniteList.tpe(Type.int))
            _ <- Outcome.assertEquals(tf.outType, Type.pair(InfiniteList.tpe(Type.int), Type.int))
          } yield ()
        },

      "infer types of InfiniteList.fix[Int] > InfiniteList.unfix[Int]" ->
        testInferredTypes(InfiniteList.fix[Int] > InfiniteList.unfix[Int]) { tf =>
          for {
            _ <- Outcome.assertEquals(tf.inType,  Type.pair(Type.int, InfiniteList.tpe(Type.int)))
            _ <- Outcome.assertEquals(tf.outType, Type.pair(Type.int, InfiniteList.tpe(Type.int)))
          } yield ()
        },

      "infer types of InfiniteList.unfix[Int] > InfiniteList.fix[Int]" ->
        testInferredTypes(InfiniteList.unfix[Int] > InfiniteList.fix[Int]) { tf =>
          for {
            _ <- Outcome.assertEquals(tf.inType,  InfiniteList.tpe(Type.int))
            _ <- Outcome.assertEquals(tf.outType, InfiniteList.tpe(Type.int))
          } yield ()
        },

      "infer types of recur" ->
        testInferredTypes(Fun.recur[String, Int]) { tf =>
          (tf.inType, tf.outType) match {
            case (Type.Pair(Type.RecCall(Type.AbstractType(a), Type.AbstractType(b)), Type.AbstractType(c)), Type.AbstractType(d)) if a == c && b == d =>
              Outcome.success(())
            case other =>
              Outcome.failure(s"Unexpected types (${tf.inType}, ${tf.outType})")
          }
        },

      "infer types of assocLR > snd(swap)" ->
        testInferredTypes(Fun.assocLR > Fun.snd(Fun.swap)) { tf =>
          (tf.inType, tf.outType) match {
            case (
              Type.Pair(Type.Pair(Type.AbstractType(a), Type.AbstractType(b)), Type.AbstractType(c)),
              Type.Pair(Type.AbstractType(d), Type.Pair(Type.AbstractType(e), Type.AbstractType(f)))
            ) if a == d && b == f && c == e =>
              Outcome.success(())
            case other =>
              Outcome.failure(s"Unexpected types (${tf.inType}, ${tf.outType})")
          }
        },

      "infer types of id > id" ->
        testInferredTypes(Fun.id > Fun.id) { tf =>
          (tf.inType, tf.outType) match {
            case (
              Type.AbstractType(a),
              Type.AbstractType(b),
            ) if a == b =>
              Outcome.success(())
            case other =>
              Outcome.failure(s"Unexpected types (${tf.inType}, ${tf.outType})")
          }
        },

      "infer types of id > id > id" ->
        testInferredTypes(Fun.id > Fun.id > Fun.id) { tf =>
          (tf.inType, tf.outType) match {
            case (
              Type.AbstractType(a),
              Type.AbstractType(b),
            ) if a == b =>
              Outcome.success(())
            case other =>
              Outcome.failure(s"Unexpected types (${tf.inType}, ${tf.outType})")
          }
        },

      "infer types of id > id > id > id" ->
        testInferredTypes(Fun.id > Fun.id > Fun.id > Fun.id) { tf =>
          (tf.inType, tf.outType) match {
            case (
              Type.AbstractType(a),
              Type.AbstractType(b),
            ) if a == b =>
              Outcome.success(())
            case other =>
              Outcome.failure(s"Unexpected types (${tf.inType}, ${tf.outType})")
          }
        },

      "infer types of id > id > id > id > id" ->
        testInferredTypes(Fun.id > Fun.id > Fun.id > Fun.id > Fun.id) { tf =>
          (tf.inType, tf.outType) match {
            case (
              Type.AbstractType(a),
              Type.AbstractType(b),
            ) if a == b =>
              Outcome.success(())
            case other =>
              Outcome.failure(s"Unexpected types (${tf.inType}, ${tf.outType})")
          }
        },

      "infer types of (id > id > id) > (id > id > id)" ->
        testInferredTypes((Fun.id > Fun.id > Fun.id) > (Fun.id > Fun.id > Fun.id)) { tf =>
          (tf.inType, tf.outType) match {
            case (
              Type.AbstractType(a),
              Type.AbstractType(b),
            ) if a == b =>
              Outcome.success(())
            case other =>
              Outcome.failure(s"Unexpected types (${tf.inType}, ${tf.outType})")
          }
        },

      "infer types of swap > swap > swap" ->
        testInferredTypes(Fun.swap > Fun.swap > Fun.swap) { tf =>
          (tf.inType, tf.outType) match {
            case (
              Type.Pair(Type.AbstractType(a), Type.AbstractType(b)),
              Type.Pair(Type.AbstractType(c), Type.AbstractType(d)),
            ) if a == d && b == c =>
              Outcome.success(())
            case other =>
              Outcome.failure(s"Unexpected types (${tf.inType}, ${tf.outType})")
          }
        },

      "infer types of swap > swap > swap > swap" ->
        testInferredTypes(Fun.swap > Fun.swap > Fun.swap > Fun.swap) { tf =>
          (tf.inType, tf.outType) match {
            case (
              Type.Pair(Type.AbstractType(a), Type.AbstractType(b)),
              Type.Pair(Type.AbstractType(c), Type.AbstractType(d)),
            ) if a == c && b == d =>
              Outcome.success(())
            case other =>
              Outcome.failure(s"Unexpected types (${tf.inType}, ${tf.outType})")
          }
        },

      "infer types of assocLR > assocLR > assocRL > assocRL" ->
        testInferredTypes(Fun.assocLR > Fun.assocLR > Fun.assocRL > Fun.assocRL) { tf =>
          (tf.inType, tf.outType) match {
            case (
              Type.Pair(Type.Pair(Type.Pair(Type.AbstractType(a), Type.AbstractType(b)), Type.AbstractType(c)), Type.AbstractType(d)),
              Type.Pair(Type.Pair(Type.Pair(Type.AbstractType(e), Type.AbstractType(f)), Type.AbstractType(g)), Type.AbstractType(h))
            ) if a == e && b == f && c == g && d == h =>
              Outcome.success(())
            case other =>
              Outcome.failure(s"Unexpected types (${tf.inType}, ${tf.outType})")
          }
        },

      "infer types of assocLR > snd(swap) > assocRL" ->
        testInferredTypes(Fun.assocLR > Fun.snd(Fun.swap) > Fun.assocRL) { tf =>
          (tf.inType, tf.outType) match {
            case (
              Type.Pair(Type.Pair(Type.AbstractType(a), Type.AbstractType(b)), Type.AbstractType(c)),
              Type.Pair(Type.Pair(Type.AbstractType(d), Type.AbstractType(e)), Type.AbstractType(f))
            ) if a == d && b == f && c == e =>
              Outcome.success(())
            case other =>
              Outcome.failure(s"Unexpected types (${tf.inType}, ${tf.outType})")
          }
        },

      "infer types of (assocLR > snd(swap)) > (assocRL > fst(swap))" ->
        testInferredTypes((Fun.assocLR > Fun.snd(Fun.swap)) > (Fun.assocRL > Fun.fst(Fun.swap))) { tf =>
          (tf.inType, tf.outType) match {
            case (
              Type.Pair(Type.Pair(Type.AbstractType(a), Type.AbstractType(b)), Type.AbstractType(c)),
              Type.Pair(Type.Pair(Type.AbstractType(d), Type.AbstractType(e)), Type.AbstractType(f))
            ) if a == e && b == f && c == d =>
              Outcome.success(())
            case other =>
              Outcome.failure(s"Unexpected types (${tf.inType}, ${tf.outType})")
          }
        },

      "infer types of snd(InfiniteList.unfix[Int] > swap) > assocRL > fst(recur)" ->
        testInferredTypes(Fun.snd(InfiniteList.unfix[Int] > Fun.swap) > Fun.assocRL > Fun.fst(Fun.recur)) { tf =>
          (tf.inType, tf.outType) match {
            case (
              Type.Pair(Type.RecCall(a, b), c),
              Type.Pair(x, y)
            ) =>
              for {
                _ <- assertEquals(c, InfiniteList.tpe(Type.int))
                _ <- assertEquals(x, b)
                _ <- assertEquals(y, Type.int)
                _ <- assertEquals(a, InfiniteList.tpe(Type.int))
              } yield ()
            case other =>
              Outcome.failure(s"Unexpected types (${tf.inType}, ${tf.outType})")
          }
        },

      "infer types of rec(recur)" ->
        testInferredTypes(Fun.rec(Fun.recur)) { tf =>
          (tf.inType, tf.outType) match {
            case (Type.AbstractType(a), Type.AbstractType(b)) =>
              Outcome.success(())
            case other =>
              Outcome.failure(s"Unexpected types (${tf.inType}, ${tf.outType})")
          }
        },

      "infer types of InfiniteList.sum" ->
        testInferredTypes(InfiniteList.sum) { tf =>
          for {
            _ <- Outcome.assertEquals(tf.inType, InfiniteList.tpe(Type.int))
            _ <- Outcome.assertEquals(tf.outType, Type.int)
          } yield ()
        },

      "infer types of InfiniteList.map(intToString)" ->
        testInferredTypes(InfiniteList.map(Fun.intToString)) { tf =>
          for {
            _ <- Outcome.assertEquals(tf.inType, InfiniteList.tpe(Type.int))
            _ <- Outcome.assertEquals(tf.outType, InfiniteList.tpe(Type.string))
          } yield ()
        },

      "infer types of InfiniteList.unfix_[Int] > fst(intToString)" ->
        testInferredTypes(InfiniteList.unfix_[Int] > Fun.fst(intToString)) { tf =>
          for {
            _ <- Outcome.assertEquals(tf.outType, Type.pair(Type.string, InfiniteList.tpe(Type.int)))
            _ <- Outcome.assertEquals(tf.inType, InfiniteList.tpe(Type.int))
          } yield ()
        }.pending,

      "infer types of InfiniteList.map_(intToString)" ->
        testInferredTypes(InfiniteList.map_(Fun.intToString)) { tf =>
          for {
            _ <- Outcome.assertEquals(tf.inType, InfiniteList.tpe(Type.int))
            _ <- Outcome.assertEquals(tf.outType, InfiniteList.tpe(Type.string))
          } yield ()
        }.pending,

      "infer types of List.map(intToString)" ->
        testInferredTypes(List.map(Fun.intToString)) { tf =>
          for {
            _ <- Outcome.assertEquals(tf.inType, List.tpe(Type.int))
            _ <- Outcome.assertEquals(tf.outType, List.tpe(Type.string))
          } yield ()
        }.pending,

      "infer types of List.map_(intToString)" ->
        testInferredTypes(List.map_(Fun.intToString)) { tf =>
          for {
            _ <- Outcome.assertEquals(tf.inType, List.tpe(Type.int))
            _ <- Outcome.assertEquals(tf.outType, List.tpe(Type.string))
          } yield ()
        }.pending,

      "infer types of List.map(List.map(intToString))" ->
        testInferredTypes(List.map(List.map(Fun.intToString))(using List.tag[Int], List.tag[String])) { tf =>
          for {
            _ <- Outcome.assertEquals(tf.inType, List.tpe(List.tpe(Type.int)))
            _ <- Outcome.assertEquals(tf.outType, List.tpe(List.tpe(Type.string)))
          } yield ()
        }.pending,

      "infer types of List.map_(List.map_(intToString))" ->
        testInferredTypes(List.map_(List.map_(Fun.intToString))) { tf =>
          for {
            _ <- Outcome.assertEquals(tf.inType, List.tpe(List.tpe(Type.int)))
            _ <- Outcome.assertEquals(tf.outType, List.tpe(List.tpe(Type.string)))
          } yield ()
        }.pending,

      "infer types of nested Fix types: countNils" -> {
        import List.{given TypeTag[List]}

        val countNils: Fun[Fix[List], Int] =
          Fun.recFun { countNils => x =>
            val y = Fun.unfix[List](x)
            val z = Fun.unfix[ListF[Fix[List], *]](using ListF.typeTag[Fix[List]])(y)
            z switch {
              case Left(u) =>
                Fun.constInt(1)(u)
              case Right(w <*> ws) =>
                Fun.addInts(countNils(w) <*> countNils(Fun.fix[List](ws)))
            }
          }

        testInferredTypes(countNils) { tf =>
          for {
            _ <- Outcome.assertEquals(tf.inType, Type.fix(List.tpe))
            _ <- Outcome.assertEquals(tf.outType, Type.int)
          } yield ()
        }
      }.pending,

      "infer types of NonEmptyTree.map_(intToString)" ->
        testInferredTypes(NonEmptyTree.map_(Fun.intToString)) { tf =>
          for {
            _ <- Outcome.assertEquals(tf.inType, NonEmptyTree.tpe(Type.int))
            _ <- Outcome.assertEquals(tf.outType, NonEmptyTree.tpe(Type.string))
          } yield ()
        }.withTimeout(5.seconds).pending,

      "infer types of NonEmptyTree.map(intToString)" ->
        testInferredTypes(NonEmptyTree.map(Fun.intToString)) { tf =>
          for {
            _ <- Outcome.assertEquals(tf.inType, NonEmptyTree.tpe(Type.int))
            _ <- Outcome.assertEquals(tf.outType, NonEmptyTree.tpe(Type.string))
          } yield ()
        }.pending,

      "infer types of Bifunctor[[x, y] =>> (Const[x, y], (y, x))].bimap" -> {
        type F[X, Y] = (Const[X, Y], (Y, X))

        object F {
          def lmap[A, B, C](f: Fun[A, C]): Fun[F[A, B], F[C, B]] =
            Fun.par(
              Const.bifunctorConst.lmap(f),
              Swap.bifunctorSwap[(*, *)].lmap(f),
            )

          def rmap[A, B, D](g: Fun[B, D]): Fun[F[A, B], F[A, D]] =
            Fun.par(
              Const.bifunctorConst.rmap(g),
              Swap.bifunctorSwap[(*, *)].rmap(g)
            )

          def bimap[A, B, C, D](f: Fun[A, C], g: Fun[B, D]): Fun[F[A, B], F[C, D]] =
            lmap(f) > rmap(g)

          val tpe: TypeFun[● × ●, ●] =
            TypeFun(
              Routing.par(
                Routing.dup[●],
                Routing.dup[●],
              ) > Routing.ixi > Routing.par(
                Routing.elimSnd,
                Routing.swap,
              ): Routing[● × ●, ● × (● × ●)],
              Type.pair.applyTo(PartialArgs.snd(PartialArgs(Type.pair))),
            )

          def tpeAt(a: Type, b: Type): Type =
            TypeFun.appFst(tpe, TypeFun.fromExpr(a)).apply(b)
        }

        val f: Fun[F[Unit, Int], F[Int, String]] =
          F.bimap(Fun.constInt(0), Fun.intToString)

        testInferredTypes(f) { tf =>
          for {
            _ <- Outcome.assertEquals(tf.inType, F.tpeAt(Type.unit, Type.int))
            _ <- Outcome.assertEquals(tf.outType, F.tpeAt(Type.int, Type.string))
          } yield ()
        }
      },
    )
  }
}
