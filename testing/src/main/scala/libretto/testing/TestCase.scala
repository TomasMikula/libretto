package libretto.testing

import libretto.testing.TestKit.dsl

sealed trait TestCase[TK <: TestKit]

object TestCase {

  sealed trait Single[TK <: TestKit] extends TestCase[TK] {
    val testKit: TK
    import testKit.Outcome
    import testKit.dsl._
    import testKit.probes.OutPort

    type O
    type X

    val body: Done -⚬ O

    val conductor: OutPort[O] => Outcome[X]

    val postStop: X => Outcome[Unit]
  }

  case class Multiple[TK <: TestKit](
    cases: List[(String, TestCase[TK])],
  ) extends TestCase[TK]

  private def make[A, B](using
    kit: TestKit,
  )(
    body0: dsl.-⚬[dsl.Done, A],
    conductor0: kit.probes.OutPort[A] => kit.Outcome[B],
    postStop0: B => kit.Outcome[Unit],
  ): TestCase[kit.type] =
    new Single[kit.type] {
      override type O = A
      override type X = B
      override val testKit = kit
      override val body = body0
      override val conductor = conductor0
      override val postStop = postStop0
    }

  def apply(using kit: TestKit)(body: dsl.-⚬[dsl.Done, kit.Assertion[dsl.Done]]): TestCase[kit.type] =
    make(body, kit.extractOutcome, kit.monadOutcome.pure)

  def apply[O](using kit: TestKit)(
    body: kit.dsl.-⚬[kit.dsl.Done, O],
    conduct: kit.probes.OutPort[O] => kit.Outcome[Unit],
  ): TestCase[kit.type] =
    make[O, Unit](body, conduct, kit.monadOutcome.pure)

  def apply[A, B](using kit: TestKit)(
    body: kit.dsl.-⚬[kit.dsl.Done, A],
    conduct: kit.probes.OutPort[A] => kit.Outcome[B],
    postStop: B => kit.Outcome[Unit],
  ): TestCase[kit.type] =
    make[A, B](body, conduct, postStop)

  def multiple[TK <: TestKit](
    cases: (String, TestCase[TK])*,
  ): TestCase[TK] =
    Multiple[TK](cases.toList)

  def interactWith[O](using kit: TestKit)(body: kit.dsl.-⚬[kit.dsl.Done, O]): InteractWith[kit.type, O] =
    InteractWith(kit, body)

  object InteractWith {
    def apply[O](kit: TestKit, body: kit.dsl.-⚬[kit.dsl.Done, O]): InteractWith[kit.type, O] =
      new InteractWith(kit, body)
  }

  class InteractWith[TK <: TestKit, O](
    val kit: TK,
    val body: kit.dsl.-⚬[kit.dsl.Done, O],
  ) {
    def via(conductor: kit.probes.OutPort[O] => kit.Outcome[Unit]): TestCase[kit.type] =
      TestCase(using kit)(body, conductor)

    def via[X](
      conductor: kit.probes.OutPort[O] => kit.Outcome[X],
      postStop: X => kit.Outcome[Unit],
    ): TestCase[kit.type] =
      TestCase(using kit)(body, conductor, postStop)
  }
}
