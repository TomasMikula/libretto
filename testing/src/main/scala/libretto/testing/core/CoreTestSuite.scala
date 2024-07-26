package libretto.testing.core

import libretto.lambda.util.SourcePos
import libretto.testing.{TestCase, TestSuite}
import libretto.testing.TestKit.dsl

trait AbstractCoreTestSuite[TK <: CoreTestKit] extends TestSuite[TK] {

  extension (TC: TestCase.type)
    def awaitDone(using kit: CoreTestKit)(
      body: dsl.-⚬[dsl.Done, dsl.Done],
    )(using pos: SourcePos): TestCase.Single[kit.type] =
      TestCase[dsl.Done](body, _.expectDone)

}

trait CoreTestSuite extends AbstractCoreTestSuite[CoreTestKit]
