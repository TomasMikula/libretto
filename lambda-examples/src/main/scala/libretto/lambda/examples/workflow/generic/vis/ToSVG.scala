package libretto.lambda.examples.workflow.generic.vis

trait ToSVG[A] {
  extension (a: A)
    def toSVG: SVGElem
}
