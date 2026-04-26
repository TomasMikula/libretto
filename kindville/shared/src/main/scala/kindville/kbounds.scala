package kindville

/** Turns a code for a kind, such as
  *
  * ```
  * (* -> *) -> *
  * ```
  *
  * into a type upper bound, such as
  *
  * ```
  * [_ <: [_] =>> Any] =>> Any
  * ```
  */
type KBound[K] <: AnyKind = K match
  case * =>
    Any
  case (ks ->> l) =>
    ks match
      case TNil =>
        KBound[l]
      case k0 :: t =>
        t match
          case TNil => [_ <: KBound[k0]] =>> KBound[l]
          case k1 :: t =>
            t match
              case TNil => [_ <: KBound[k0], _ <: KBound[k1]] =>> KBound[l]
              case k2 :: t =>
                t match
                  case TNil => [_ <: KBound[k0], _ <: KBound[k1], _ <: KBound[k2]] =>> KBound[l]

type KBounds[K] <: AnyKind = K match
  case * =>
    KBound[kindville.*]
  case (ks ->> l) =>
    KBound[ks ->> l]
  case _ =>
    KBoundList[K]

type KBoundList[Ks] = Ks match
  case TNil =>
    TNil
  case k0 :: ks =>
    KBound[k0] :: KBoundList[ks]
