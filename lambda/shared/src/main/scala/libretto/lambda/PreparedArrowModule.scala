package libretto.lambda

/** Provides `SymmetricSemigroupalCategory` instance for `Prepared[A, B]` (= `Obj[A] => (A -> B, Obj[B])`),
 * when there is only a `NarrowSymmetricSemigroupalCategory` for `->`.
 */
final class PreparedArrowModule[Obj[_], ->[_, _], **[_, _]](using
  cat: NarrowSymmetricSemigroupalCategory[Obj, ->, **],
  objects: Unzippable[**, Obj],
) {
  /** Builds an underlying arrow and its output witness from its input witness. */
  final case class Prepared[A, B](run: Obj[A] => (A -> B, Obj[B]))

  def lift[A, B](f: A -> B)(using b: Obj[B]): Prepared[A, B] =
    Prepared(_ => (f, b))

  given SymmetricSemigroupalCategory[Prepared, **] with {
    override def id[A]: Prepared[A, A] =
      Prepared(a => (cat.id[A](using a), a))

    override def andThen[A, B, C](f: Prepared[A, B], g: Prepared[B, C]): Prepared[A, C] =
      Prepared { a =>
        val (f1, b) = f.run(a)
        val (g1, c) = g.run(b)
        (cat.narrowAndThen(f1, g1)(using a, b, c), c)
      }

    override def par[A1, A2, B1, B2](f: Prepared[A1, B1], g: Prepared[A2, B2]): Prepared[A1 ** A2, B1 ** B2] =
      Prepared { a =>
        val (a1, a2) = objects.unzip(a)
        val (f1, b1) = f.run(a1)
        val (g1, b2) = g.run(a2)
        (cat.narrowPar(f1, g1)(using a1, a2, b1, b2), cat.tensor(b1, b2))
      }

    override def swap[A, B]: Prepared[A ** B, B ** A] =
      Prepared { ab =>
        val (a, b) = objects.unzip(ab)
        (cat.swap[A, B](using a, b), cat.tensor(b, a))
      }

    override def assocLR[A, B, C]: Prepared[(A ** B) ** C, A ** (B ** C)] =
      Prepared { ab_c =>
        val (ab, c) = objects.unzip(ab_c)
        val (a, b) = objects.unzip(ab)
        (cat.assocLR[A, B, C](using a, b, c), cat.tensor(a, cat.tensor(b, c)))
      }

    override def assocRL[A, B, C]: Prepared[A ** (B ** C), (A ** B) ** C] =
      Prepared { a_bc =>
        val (a, bc) = objects.unzip(a_bc)
        val (b, c) = objects.unzip(bc)
        (cat.assocRL[A, B, C](using a, b, c), cat.tensor(cat.tensor(a, b), c))
      }
  }
}
