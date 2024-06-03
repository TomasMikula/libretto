package libretto.lambda

trait Distribution[->[_, _], **[_, _], ++[_, _]] {
  def distLR[A, B, C]: (A ** (B ++ C)) -> ((A ** B) ++ (A ** C))
  def distRL[A, B, C]: ((A ++ B) ** C) -> ((A ** C) ++ (B ** C))
}
