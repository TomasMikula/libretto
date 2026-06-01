package libretto.testing.puro

import libretto.lambda.util.SourcePos
import libretto.testing.{TestCase, TestSuite}
import libretto.testing.TestKit.dsl

trait AbstractPuroTestSuite[TK <: PuroTestKit] extends TestSuite[TK] {

  extension (TC: TestCase.type)
    def awaitDone(using kit: PuroTestKit)(
      body: dsl.-⚬[dsl.Done, dsl.Done],
    )(using pos: SourcePos): TestCase.Single[kit.type] =
      TestCase[dsl.Done](body, _.expectDone)

}

trait PuroTestSuite extends AbstractPuroTestSuite[PuroTestKit]
