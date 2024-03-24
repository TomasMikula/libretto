package kindville

private[kindville] sealed trait Kind:
  type Label

private[kindville] object Kind:
  type Of[K] = Kind { type Label = K }

  case object Tp extends Kind {
    override type Label = *
  }

  case class Arr[Ks, L](
    paramKinds: Kinds.Of[Ks],
    outKind: Kind.Of[L],
  ) extends Kind {
    override type Label = Ks ->> L
  }

  def arr(ks: Kinds, l: Kind): Kind.Of[ks.Label ->> l.Label] =
    Arr(ks, l)

private[kindville] sealed trait Kinds:
  type Label

  def ::(k: Kind): Kinds.Of[k.Label :: Label] =
    Kinds.Cons(k, this)

  def toList: List[Kind] =
    this match
      case Kinds.Empty      => Nil
      case Kinds.Cons(h, t) => h :: t.toList

private[kindville] object Kinds:
  type Of[Ks] = Kinds { type Label = Ks }

  case object Empty extends Kinds {
    override type Label = TNil
  }

  case class Cons[K, Ks](
    head: Kind.Of[K],
    tail: Kinds.Of[Ks],
  ) extends Kinds {
    override type Label = K :: Ks
  }
