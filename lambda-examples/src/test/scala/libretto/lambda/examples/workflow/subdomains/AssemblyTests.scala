package libretto.lambda.examples.workflow.subdomains

import libretto.lambda.examples.workflow.subdomains
import org.scalatest.funsuite.AnyFunSuite

/**
 * Tests that the programs successfully assemble.
 */
class AssemblyTests extends AnyFunSuite {
  test("backgroundCheck") {
    val prg =
      backgroundcheck.backgroundCheck
  }

  test("equipmentRequest") {
    val prg =
      equipmentRequest.equipmentRequest
  }
}
