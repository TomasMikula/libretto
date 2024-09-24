package libretto.lambda.examples.workflow.generic.vis

sealed trait IOLayout[I, O] {
  import IOLayout.*

  def pixelBreadth: Px
  def inEdge: EdgeLayout[I]
  def outEdge: EdgeLayout[O]
  def *(k: Int): IOLayout[I, O]

  def separate: (EdgeLayout[I], EdgeLayout[O]) =
    (inEdge, outEdge)
}

object IOLayout {
  sealed trait EdgeLayout[X] {
    def pixelBreadth: Px
    def *(k: Int): EdgeLayout[X]

    /** Returns the offset and breadth of the given wire on this edge. */
    def coordsOf(wire: WirePick[X]): (Px, Px)
  }

  object EdgeLayout {
    case class Unimplemented[X](pixelBreadth: Px) extends EdgeLayout[X] {
      override def *(k: Int): EdgeLayout[X] =
        Unimplemented(pixelBreadth * k)

      override def coordsOf(wire: WirePick[X]): (Px, Px) = (
        Px(pixelBreadth.pixels * 6 / 13),
        Px(pixelBreadth.pixels     / 13),
      )
    }

    case class Par[∙[_, _], X1, X2](
      l1: EdgeLayout[X1],
      l2: EdgeLayout[X2],
    ) extends EdgeLayout[X1 ∙ X2] {
      override def pixelBreadth: Px =
        l1.pixelBreadth + l2.pixelBreadth

      override def *(k: Int): EdgeLayout[X1 ∙ X2] =
        Par(l1 * k, l2 * k)

      override def coordsOf(wire: WirePick[X1 ∙ X2]): (Px, Px) =
        wire.switch(
          caseId = (ev: (X1 ∙ X2) =:= Wire) ?=> ???,
          caseInl = [∘[_, _], A, B] => (ev: (X1 ∙ X2) =:= (A ∘ B)) ?=> (fst: WirePick[A]) => {
            l1
              .asInstanceOf[EdgeLayout[A]] // XXX: unsound without knowing that ∙ and ∘ are class types
              .coordsOf(fst)
          },
          caseInr = [∘[_, _], A, B] => (ev: (X1 ∙ X2) =:= (A ∘ B)) ?=> (snd: WirePick[B]) => {
            val (offset, breadth) = l2
              .asInstanceOf[EdgeLayout[B]] // XXX: unsound without knowing that ∙ and ∘ are class types
              .coordsOf(snd)
            (offset + l1.pixelBreadth, breadth)
          },
        )
    }

    case class SingleWire(pre: Px, wire: Px, post: Px) extends EdgeLayout[Wire] {
      override def pixelBreadth: Px = pre + wire + post
      override def *(k: Int): EdgeLayout[Wire] = SingleWire(pre * k, wire * k, post * k)

      override def coordsOf(pick: WirePick[Wire]): (Px, Px) =
        pick.switch(
          caseId = (pre, wire),
          caseInl = [∘[_, _], A, B] => (ev: Wire =:= (A ∘ B)) ?=> _ => Wire.isNotBinary[∘, A, B],
          caseInr = [∘[_, _], A, B] => (ev: Wire =:= (A ∘ B)) ?=> _ => Wire.isNotBinary[∘, A, B],
        )
    }

    def wire(pre: Px, wire: Px, post: Px): EdgeLayout[Wire] =
      SingleWire(pre, wire, post)

    def pair[X, Y](x: EdgeLayout[X], y: EdgeLayout[Y]): EdgeLayout[(X, Y)] =
      Par(x, y)

    // TODO: for soundness, require evidence that ∙ is a class type
    def split[∙[_, _], X1, X2](x: EdgeLayout[X1 ∙ X2]): (EdgeLayout[X1], EdgeLayout[X2]) =
      x match
        case Par(l1, l2) => (l1, l2)
        case Unimplemented(pixelBreadth) =>
          val b1 = pixelBreadth.pixels / 2
          val b2 = pixelBreadth.pixels - b1
          (Unimplemented(Px(b1)), Unimplemented(Px(b2)))
        case SingleWire(pre, wire, post) =>
          throw AssertionError(s"Impossible Wire =:= (X1 ∙ X2). Unless ∙ is not a class type.")
  }

  case class Unimplemented[X, Y](pixelBreadth: Px) extends IOLayout[X, Y] {
    override def inEdge: EdgeLayout[X] =
      EdgeLayout.Unimplemented(pixelBreadth)

    override def outEdge: EdgeLayout[Y] =
      EdgeLayout.Unimplemented(pixelBreadth)

    override def *(k: Int): IOLayout[X, Y] =
      require(k > 0)
      Unimplemented(pixelBreadth * k)
  }

  case class Separate[I, O](
    inEdge: EdgeLayout[I],
    outEdge: EdgeLayout[O],
  ) extends IOLayout[I, O] {
    override def pixelBreadth: Px =
      Px.max(inEdge.pixelBreadth, outEdge.pixelBreadth)

    override def *(k: Int): IOLayout[I, O] =
      Separate(inEdge * k, outEdge * k)
  }

  case class Par[∙[_, _], I1, I2, O1, O2](
    l1: IOLayout[I1, O1],
    l2: IOLayout[I2, O2],
  ) extends IOLayout[I1 ∙ I2, O1 ∙ O2] {
    override def pixelBreadth: Px =
      l1.pixelBreadth + l2.pixelBreadth

    override def inEdge: EdgeLayout[I1 ∙ I2] =
      EdgeLayout.Par(l1.inEdge, l2.inEdge)

    override def outEdge: EdgeLayout[O1 ∙ O2] =
      EdgeLayout.Par(l1.outEdge, l2.outEdge)

    override def *(k: Int): IOLayout[I1 ∙ I2, O1 ∙ O2] =
      require(k > 0)
      Par(l1 * k, l2 * k)
  }
}
