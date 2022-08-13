package libretto.testing

import libretto.testing.TestKit.dsl
import libretto.util.SourcePos

sealed trait TestCase[TK <: TestKit]

object TestCase {
  sealed trait Single[TK <: TestKit] extends TestCase[TK]

  sealed trait SingleProgram[TK <: TestKit] extends Single[TK] {
    val testKit: TK
    import testKit.{ExecutionParam, Outcome}
    import testKit.dsl._
    import testKit.bridge.Execution

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

  def parameterized[A, Q, B](using kit: TestKit)(
    body0: dsl.-⚬[dsl.Done, A],
    params0: kit.ExecutionParam[Q],
    conductor0: (exn: kit.bridge.Execution) ?=> (exn.OutPort[A], Q) => kit.Outcome[B],
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

  private def apply[A, B](using kit: TestKit)(
    body0: dsl.-⚬[dsl.Done, A],
    conductor0: (exn: kit.bridge.Execution) ?=> exn.OutPort[A] => kit.Outcome[B],
    postStop0: B => kit.Outcome[Unit],
  ): TestCase[kit.type] =
    parameterized[A, Unit, B](
      body0,
      kit.ExecutionParam.unit,
      (pa, _) => conductor0(pa),
      postStop0,
    )

  def apply(using kit: TestKit)(
    body: dsl.-⚬[dsl.Done, kit.Assertion[dsl.Done]],
  )(using pos: SourcePos): TestCase[kit.type] =
    apply[kit.Assertion[dsl.Done], Unit](body, kit.extractOutcome(_), kit.monadOutcome.pure)

  def apply[O](using kit: TestKit)(
    body: kit.dsl.-⚬[kit.dsl.Done, O],
    conduct: (exn: kit.bridge.Execution) ?=> exn.OutPort[O] => kit.Outcome[Unit],
  ): TestCase[kit.type] =
    apply[O, Unit](body, conduct(_), kit.monadOutcome.pure)

  def parameterized[O, P](using kit: TestKit)(
    body: kit.dsl.-⚬[kit.dsl.Done, O],
    params: kit.ExecutionParam[P],
    conduct: (exn: kit.bridge.Execution) ?=> (exn.OutPort[O], P) => kit.Outcome[Unit],
  ): TestCase[kit.type] =
    parameterized[O, P, Unit](body, params, conduct(_, _), kit.monadOutcome.pure)

  def multiple[TK <: TestKit](
    cases: (String, TestCase[TK])*,
  ): TestCase[TK] =
    Multiple[TK](cases.toList)

  def testOutcome[TK <: TestKit](using kit: TestKit)(
    body: => kit.Outcome[Unit],
  ): TestCase[kit.type] =
    new OutcomeOnly[kit.type](kit, () => body)

  def configure[P](using kit: TestKit)(
    params: kit.ExecutionParam[P],
  ): Configure[kit.type, P] =
    Configure(kit, params)

  def interactWith[O](using kit: TestKit)(body: kit.dsl.-⚬[kit.dsl.Done, O]): InteractWith[kit.type, O] =
    InteractWith(kit, body)

  class Configure[TK <: TestKit, P](
    val kit: TK,
    val params: kit.ExecutionParam[P],
  ) {
    def interactWith[O](body: kit.dsl.-⚬[kit.dsl.Done, O]): InteractWithConfigured[kit.type, O, P] =
      InteractWithConfigured(kit, body, params)
  }

  class InteractWith[TK <: TestKit, O](
    val kit: TK,
    val body: kit.dsl.-⚬[kit.dsl.Done, O],
  ) {
    def via(conductor: (exn: kit.bridge.Execution) ?=> exn.OutPort[O] => kit.Outcome[Unit]): TestCase[kit.type] =
      TestCase(using kit)(body, conductor(_))

    def via[X](
      conductor: (exn: kit.bridge.Execution) ?=> exn.OutPort[O] => kit.Outcome[X],
      postStop: X => kit.Outcome[Unit],
    ): TestCase[kit.type] =
      TestCase(using kit)(body, conductor(_), postStop)
  }

  class InteractWithConfigured[TK <: TestKit, O, P](
    val kit: TK,
    val body: kit.dsl.-⚬[kit.dsl.Done, O],
    val params: kit.ExecutionParam[P],
  ) {
    def via(conductor: (exn: kit.bridge.Execution) ?=> (exn.OutPort[O], P) => kit.Outcome[Unit]): TestCase[kit.type] =
      TestCase.parameterized(using kit)(body, params, conductor(_, _))

    def via[X](
      conductor: (exn: kit.bridge.Execution) ?=> (exn.OutPort[O], P) => kit.Outcome[X],
      postStop: X => kit.Outcome[Unit],
    ): TestCase[kit.type] =
      TestCase.parameterized(using kit)(body, params, conductor(_, _), postStop)
  }
}
