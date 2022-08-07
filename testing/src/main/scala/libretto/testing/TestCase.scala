package libretto.testing

import libretto.testing.TestKit.dsl

sealed trait TestCase[TK <: TestKit]

object TestCase {
  sealed trait Single[TK <: TestKit] extends TestCase[TK]

  sealed trait SingleProgram[TK <: TestKit] extends Single[TK] {
    val testKit: TK
    import testKit.{ExecutionParam, Outcome}
    import testKit.dsl._
    import testKit.probes.Execution

    type O
    type P
    type X

    val body: Done -⚬ O

    val params: ExecutionParam[P]

    val conductor: (exn: Execution) ?=> (exn.OutPort[O], P) => Outcome[X]

    val postStop: X => Outcome[Unit]
  }

  class OutcomeOnly[TK <: TestKit](
    val testKit: TK,
    val body: () => testKit.Outcome[Unit],
  ) extends Single[TK]

  case class Multiple[TK <: TestKit](
    cases: List[(String, TestCase[TK])],
  ) extends TestCase[TK]

  private def makeWithParams[A, Q, B](using
    kit: TestKit,
  )(
    body0: dsl.-⚬[dsl.Done, A],
    params0: kit.ExecutionParam[Q],
    conductor0: (exn: kit.probes.Execution) ?=> (exn.OutPort[A], Q) => kit.Outcome[B],
    postStop0: B => kit.Outcome[Unit],
  ): TestCase[kit.type] =
    new SingleProgram[kit.type] {
      override type O = A
      override type P = Q
      override type X = B
      override val testKit: kit.type = kit
      override val body = body0
      override val params = params0
      override val conductor = conductor0(_, _)
      override val postStop = postStop0
    }

  private def make[A, B](using
    kit: TestKit,
  )(
    body0: dsl.-⚬[dsl.Done, A],
    conductor0: (exn: kit.probes.Execution) ?=> exn.OutPort[A] => kit.Outcome[B],
    postStop0: B => kit.Outcome[Unit],
  ): TestCase[kit.type] =
    makeWithParams[A, Unit, B](
      body0,
      kit.ExecutionParam.unit,
      (pa, _) => conductor0(pa),
      postStop0,
    )

  def apply(using kit: TestKit)(body: dsl.-⚬[dsl.Done, kit.Assertion[dsl.Done]]): TestCase[kit.type] =
    make(body, kit.extractOutcome(_), kit.monadOutcome.pure)

  def apply[O](using kit: TestKit)(
    body: kit.dsl.-⚬[kit.dsl.Done, O],
    conduct: (exn: kit.probes.Execution) ?=> exn.OutPort[O] => kit.Outcome[Unit],
  ): TestCase[kit.type] =
    make[O, Unit](body, conduct(_), kit.monadOutcome.pure)

  def apply[A, B](using kit: TestKit)(
    body: kit.dsl.-⚬[kit.dsl.Done, A],
    conduct: (exn: kit.probes.Execution) ?=> exn.OutPort[A] => kit.Outcome[B],
    postStop: B => kit.Outcome[Unit],
  ): TestCase[kit.type] =
    make[A, B](body, conduct(_), postStop)

  def multiple[TK <: TestKit](
    cases: (String, TestCase[TK])*,
  ): TestCase[TK] =
    Multiple[TK](cases.toList)

  def testOutcome[TK <: TestKit](using kit: TestKit)(
    body: => kit.Outcome[Unit],
  ): TestCase[kit.type] =
    new OutcomeOnly[kit.type](kit, () => body)

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
    def via(conductor: (exn: kit.probes.Execution) ?=> exn.OutPort[O] => kit.Outcome[Unit]): TestCase[kit.type] =
      TestCase(using kit)(body, conductor(_))

    def via[X](
      conductor: (exn: kit.probes.Execution) ?=> exn.OutPort[O] => kit.Outcome[X],
      postStop: X => kit.Outcome[Unit],
    ): TestCase[kit.type] =
      TestCase(using kit)(body, conductor(_), postStop)
  }
}
