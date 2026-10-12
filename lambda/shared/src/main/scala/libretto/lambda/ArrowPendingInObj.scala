package libretto.lambda

case class ArrowPendingInObj[->[_, _], Obj[_], A, B](
  run: Obj[A] => (A -> B, Obj[B])
)

infix type pendingIn[->[_, _], Obj[_]] =
  [A, B] =>> ArrowPendingInObj[->, Obj, A, B]

object ArrowPendingInObj {

  def lift[->[_, _], A, B](f: A -> B)[Obj[_]](using p: -> Preserves Obj): ArrowPendingInObj[->, Obj, A, B] =
    ArrowPendingInObj(a => (f, p(f)(using a)))

  def const[->[_, _], A, B](f: A -> B)[Obj[_]](using b: Obj[B]): ArrowPendingInObj[->, Obj, A, B] =
    ArrowPendingInObj(_ => (f, b))

  given [->[_, _], Obj[_], **[_, _]] => (
    cat: NarrowSymmetricSemigroupalCategory[Obj, ->, **],
    objects: Unzippable[**, Obj],
  ) => SymmetricSemigroupalCategory[-> pendingIn Obj, **] =
    new SymmetricSemigroupalCategory[-> pendingIn Obj, **] {
      override def id[A]: (-> pendingIn Obj)[A, A] =
        ArrowPendingInObj(a => (cat.id[A](using a), a))

      override def andThen[A, B, C](f: (-> pendingIn Obj)[A, B], g: (-> pendingIn Obj)[B, C]): (-> pendingIn Obj)[A, C] =
        ArrowPendingInObj { a =>
          val (f1, b) = f.run(a)
          val (g1, c) = g.run(b)
          (cat.narrowAndThen(f1, g1)(using a, b, c), c)
        }

      override def par[A1, A2, B1, B2](f: (-> pendingIn Obj)[A1, B1], g: (-> pendingIn Obj)[A2, B2]): (-> pendingIn Obj)[A1 ** A2, B1 ** B2] =
        ArrowPendingInObj { a =>
          val (a1, a2) = objects.unzip(a)
          val (f1, b1) = f.run(a1)
          val (g1, b2) = g.run(a2)
          (cat.narrowPar(f1, g1)(using a1, a2, b1, b2), cat.tensor(b1, b2))
        }

      override def swap[A, B]: (-> pendingIn Obj)[A ** B, B ** A] =
        ArrowPendingInObj { ab =>
          val (a, b) = objects.unzip(ab)
          (cat.swap[A, B](using a, b), cat.tensor(b, a))
        }

      override def assocLR[A, B, C]: (-> pendingIn Obj)[(A ** B) ** C, A ** (B ** C)] =
        ArrowPendingInObj { ab_c =>
          val (ab, c) = objects.unzip(ab_c)
          val (a, b) = objects.unzip(ab)
          (cat.assocLR[A, B, C](using a, b, c), cat.tensor(a, cat.tensor(b, c)))
        }

      override def assocRL[A, B, C]: (-> pendingIn Obj)[A ** (B ** C), (A ** B) ** C] =
        ArrowPendingInObj { a_bc =>
          val (a, bc) = objects.unzip(a_bc)
          val (b, c) = objects.unzip(bc)
          (cat.assocRL[A, B, C](using a, b, c), cat.tensor(cat.tensor(a, b), c))
        }
    }

}
