package libretto.lambda

/** Category with n-ary coproducts. */
trait CocartesianNAryCategory[->[_, _], Sum[_], ||[_, _], ::[_, _]] {
  def inject[Label, A, Cases](
    i: Member[||, ::, Label, A, Cases],
  ): A -> Sum[Cases]

  def handle[Cases, R](
    h: SinkNAryNamed[->, ||, ::, Cases, R],
  ): Sum[Cases] -> R
}

object CocartesianNAryCategory {
  def fromBinary[->[_, _], ++[_, _], Sum[_], ||[_, _], ::[_, _]](
    cat: CocartesianSemigroupalCategory[->, ++],
    embed: [Label, A] => DummyImplicit ?=> (A -> Sum[Label :: A]),
    extract: [Label, A] => DummyImplicit ?=> Sum[Label :: A] -> A,
    peel: [Init, Label, Z] => DummyImplicit ?=> Sum[Init || (Label :: Z)] -> (Sum[Init] ++ Z),
    unpeel: [Init, Label, Z] => DummyImplicit ?=> (Sum[Init] ++ Z) -> Sum[Init || (Label :: Z)],
  ): CocartesianNAryCategory[->, Sum, ||, ::] = {
    import cat.*

    def inj[Label, A, Cases](i: Member[||, ::, Label, A, Cases]): (A -> Sum[Cases]) =
      i match
        case _: Member.Single[sep, of, l, a]              => embed[l, a]
        case _: Member.InLast[sep, of, init, lz, z]       => cat.injectR > unpeel[init, lz, z]
        case i: Member.InInit[sep, of, l, a, init, lz, z] => inj(i.i) > injectL > unpeel[init, lz, z]

    fromBinary(cat, [L, A, Cs] => inj(_), extract, peel)
  }

  def fromBinary[->[_, _], ++[_, _], Sum[_], ||[_, _], ::[_, _]](
    cat: CocartesianSemigroupalCategory[->, ++],
    inj: [Label, A, Cases] => Member[||, ::, Label, A, Cases] => (A -> Sum[Cases]),
    extract: [Label, A] => DummyImplicit ?=> Sum[Label :: A] -> A,
    peel: [Init, Label, Z] => DummyImplicit ?=> Sum[Init || (Label :: Z)] -> (Sum[Init] ++ Z),
  ): CocartesianNAryCategory[->, Sum, ||, ::] =
    FromBinary(cat, inj, extract, peel)

  private class FromBinary[->[_, _], ++[_, _], Sum[_], ||[_, _], ::[_, _]](
    cat: CocartesianSemigroupalCategory[->, ++],
    inj: [Label, A, Cases] => Member[||, ::, Label, A, Cases] => (A -> Sum[Cases]),
    extract: [Label, A] => DummyImplicit ?=> Sum[Label :: A] -> A,
    peel: [Init, Label, Z] => DummyImplicit ?=> Sum[Init || (Label :: Z)] -> (Sum[Init] ++ Z),
  ) extends CocartesianNAryCategory[->, Sum, ||, ::] {
    import cat.*

    override def inject[Label, A, Cases](
      i: Member[||, ::, Label, A, Cases],
    ): A -> Sum[Cases] =
      inj(i)

    override def handle[Cases, R](
      h: SinkNAryNamed[->, ||, ::, Cases, R],
    ): Sum[Cases] -> R =
      h match
        case s: SinkNAryNamed.Single[arr, sep, of, lbl, a, r] =>
          extract[lbl, a] > s.h
        case s: SinkNAryNamed.Snoc[arr, sep, of, init, lbl, z, r] =>
          peel[init, lbl, z] > either(handle(s.init), s.last)
  }
}
