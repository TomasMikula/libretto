package libretto.lambda

trait Distribution[->[_, _], **[_, _], ++[_, _]] {
  val cat: SemigroupalCategory[->, **]

  def distLR[A, B, C]: (A ** (B ++ C)) -> ((A ** B) ++ (A ** C))
  def distRL[A, B, C]: ((A ++ B) ** C) -> ((A ** C) ++ (B ** C))

  def distF[F[_], A, B](using F: Focus[**, F]): F[A ++ B] -> (F[A] ++ F[B]) =
    import cat.{id, andThen, fst, snd}

    F match
      case Focus.Id() => id[A ++ B]
      case Focus.Fst(f1) => andThen(fst(distF(using f1)), distRL)
      case Focus.Snd(f2) => andThen(snd(distF(using f2)), distLR)
}
