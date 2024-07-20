package libretto.testing

import libretto.ExecutionParams
import libretto.lambda.util.SourcePos
import libretto.testing.TestKit.dsl
import scala.concurrent.duration.*

sealed trait TestCase[TK <: TestKit] {
  def pending: TestCase[TK] =
    this match {
      case p: TestCase.Pending[tk] => p
      case q                       => TestCase.Pending(q)
    }
}

object TestCase {
  sealed trait Single[TK <: TestKit] extends TestCase[TK] {
    def withTimeout(d: FiniteDuration): TestCase.Single[TK]
  }

  sealed trait SingleProgram[TK <: TestKit] extends Single[TK] {
    val testKit: TK
    import testKit.{ExecutionParams, Outcome}
    import testKit.dsl.*
    import testKit.bridge.Execution

    type O
    type P
    type X

    val body: Done -⚬ O

    val params: ExecutionParams[P]

    val conductor: (exn: Execution) ?=> (exn.OutPort[O], P) => Outcome[X]

    val postStop: X => Outcome[Unit]

    val timeout: FiniteDuration

    override def withTimeout(d: FiniteDuration): TestCase.Single[TK] =
      parameterizedExecAndCheck(using testKit)(body, params, conductor(_, _), postStop, d)
  }

  class Pure[TK <: TestKit](
    val testKit: TK,
    val body: () => testKit.Outcome[Unit],
    val timeout: FiniteDuration,
  ) extends Single[TK] {
    override def withTimeout(d: FiniteDuration): TestCase.Single[TK] =
      Pure(testKit, body, d)
  }

  case class Multiple[TK <: TestKit](
    cases: List[(String, TestCase[TK])],
  ) extends TestCase[TK]

  case class Pending[TK <: TestKit](
    testCase: TestCase[TK],
  ) extends TestCase[TK]

  def parameterizedExecAndCheck[TK <: TestKit, A, Q, B](using kit: TK)(
    body0: dsl.-⚬[dsl.Done, A],
    params0: kit.ExecutionParams[Q],
    conductor0: (exn: kit.bridge.Execution) ?=> (exn.OutPort[A], Q) => kit.Outcome[B],
    postStop0: B => kit.Outcome[Unit],
    timeout0: FiniteDuration = 1.second,
  ): TestCase.Single[TK] =
    new SingleProgram[TK] {
      override type O = A
      override type P = Q
      override type X = B
      override val testKit: kit.type = kit
      override val body = body0
      override val params = params0
      override val conductor = conductor0(_, _)
      override val postStop = postStop0
      override val timeout = timeout0
    }

  private def apply[A, B](using kit: TestKit)(
    body0: dsl.-⚬[dsl.Done, A],
    conductor0: (exn: kit.bridge.Execution) ?=> exn.OutPort[A] => kit.Outcome[B],
    postStop0: B => kit.Outcome[Unit],
  ): TestCase.Single[kit.type] =
    parameterizedExecAndCheck[kit.type, A, Unit, B](
      body0,
      ExecutionParams.unit,
      (pa, _) => conductor0(pa),
      postStop0,
    )

  def apply(using kit: TestKit)(
    body: dsl.-⚬[dsl.Done, kit.Assertion[dsl.Done]],
  )(using pos: SourcePos): TestCase.Single[kit.type] =
    apply[kit.Assertion[dsl.Done], Unit](body, kit.extractOutcome(_), kit.monadOutcome.pure)

  def apply[O](using kit: TestKit)(
    body: kit.dsl.-⚬[kit.dsl.Done, O],
    conduct: (exn: kit.bridge.Execution) ?=> exn.OutPort[O] => kit.Outcome[Unit],
  ): TestCase.Single[kit.type] =
    apply[O, Unit](body, conduct(_), kit.monadOutcome.pure)

  def parameterizedExec[O, P](using kit: TestKit)(
    body: kit.dsl.-⚬[kit.dsl.Done, O],
    params: kit.ExecutionParams[P],
    conduct: (exn: kit.bridge.Execution) ?=> (exn.OutPort[O], P) => kit.Outcome[Unit],
  ): TestCase.Single[kit.type] =
    parameterizedExecAndCheck[kit.type, O, P, Unit](body, params, conduct(_, _), kit.monadOutcome.pure)

  def multiple[TK <: TestKit](
    cases: (String, TestCase[TK])*,
  ): TestCase[TK] =
    Multiple[TK](cases.toList)

  def pure[TK <: TestKit](using kit: TestKit)(
    body: => kit.Outcome[Unit],
    timeout: FiniteDuration = 1.second,
  ): TestCase[kit.type] =
    new Pure[kit.type](kit, () => body, timeout)

  @deprecated("Use pure instead", since="0.2-M5")
  def testOutcome[TK <: TestKit](using kit: TestKit)(
    body: => kit.Outcome[Unit],
    timeout: FiniteDuration = 1.second,
  ): TestCase[kit.type] =
    pure(body, timeout)

  def configure[P](using kit: TestKit)(
    params: kit.ExecutionParams[P],
  ): Configure[kit.type, P] =
    Configure(kit, params)

  def interactWith[O](using kit: TestKit)(body: kit.dsl.-⚬[kit.dsl.Done, O]): InteractWith[kit.type, O] =
    InteractWith(kit, body)

  class Configure[TK <: TestKit, P](
    val kit: TK,
    val params: kit.ExecutionParams[P],
  ) {
    def interactWith[O](body: kit.dsl.-⚬[kit.dsl.Done, O]): InteractWithConfigured[kit.type, O, P] =
      InteractWithConfigured(kit, body, params)
  }

  class InteractWith[TK <: TestKit, O](
    val kit: TK,
    val body: kit.dsl.-⚬[kit.dsl.Done, O],
  ) {
    def via(conductor: (exn: kit.bridge.Execution) ?=> exn.OutPort[O] => kit.Outcome[Unit]): TestCase.Single[kit.type] =
      TestCase(using kit)(body, conductor(_))

    def via[X](
      conductor: (exn: kit.bridge.Execution) ?=> exn.OutPort[O] => kit.Outcome[X],
      postStop: X => kit.Outcome[Unit],
    ): TestCase.Single[kit.type] =
      TestCase(using kit)(body, conductor(_), postStop)
  }

  class InteractWithConfigured[TK <: TestKit, O, P](
    val kit: TK,
    val body: kit.dsl.-⚬[kit.dsl.Done, O],
    val params: kit.ExecutionParams[P],
  ) {
    def via(conductor: (exn: kit.bridge.Execution) ?=> (exn.OutPort[O], P) => kit.Outcome[Unit]): TestCase[kit.type] =
      TestCase.parameterizedExec(using kit)(body, params, conductor(_, _))

    def via[X](
      conductor: (exn: kit.bridge.Execution) ?=> (exn.OutPort[O], P) => kit.Outcome[X],
      postStop: X => kit.Outcome[Unit],
    ): TestCase.Single[kit.type] =
      TestCase.parameterizedExecAndCheck(using kit)(body, params, conductor(_, _), postStop)
  }
}
