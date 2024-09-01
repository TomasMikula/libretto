package libretto.lambda.examples.workflow.generic.vis

import java.nio.file.{Paths, Files}
import java.nio.charset.StandardCharsets

/** Representation of a _subset_ of SVG. */
sealed trait SVG {
  import SVG.*

  def xmlTag: String
  def xmlAttributes: Map[String, String]
  def xmlContent: String | List[SVG]

  def xmlString: String =
    val content: Option[String] = xmlContent match
      case text: String     => Some(xmlTextEscape(text))
      case Nil              => None
      case elems: List[SVG] => Some(elems.map(_.xmlString).mkString("\n", "\n", "\n"))
    s"<$xmlTag"
      + xmlAttributes
        .map { case (k, v) => s"$k=\"$v\"" }
        .mkString(" ", " ", " ")
      + content.fold("/>")(str => s">$str</$xmlTag>")

  def writeTo(fileName: String): Unit =
    val fullXmlString = s"""<svg xmlns="http://www.w3.org/2000/svg">\n$xmlString\n</svg>"""
    val bytes = fullXmlString.getBytes(StandardCharsets.UTF_8)
    val path = Paths.get(fileName)
    Files.write(path, bytes)
}

object SVG {
  /* An auxiliary node for Scala representation.
   * In xml and DOM, transform is represented as an attribute on another element. */
  case class Transformed(obj: SVG.Proper, trans: Transform) extends SVG:
    override def xmlTag = obj.xmlTag
    override def xmlAttributes = obj.xmlAttributes.updated("transform", trans.attributeValue)
    override def xmlContent = obj.xmlContent

  sealed trait Proper extends SVG

  case class Text(
    value: String,
    x: Px,
    y: Px,
    fontFamily: FontFamily,
    fontSize: Px,
  ) extends SVG.Proper :
    import Px.*

    override def xmlTag =
      "text"

    override def xmlAttributes =
      Map(
        "x" -> String.valueOf(x.pixels),
        "y" -> String.valueOf(y.pixels),
        "style" -> s"font-family: ${fontFamily.cssValue}; font-size: ${fontSize.pixels}px"
      )

    override def xmlContent =
      value

  enum Transform:
    case Scale(value: Double)

    def attributeValue: String =
      this match
        case Scale(value) => s"scale($value)"

  enum FontFamily:
    case Monospace

    def cssValue: String =
      this match
        case Monospace => "monospace"

  opaque type Px = Int
  object Px {
    def apply(n: Int): Px = n

    extension (x: Px)
      def pixels: Int = x
  }

  extension (n: Int)
    def px: Px = Px(n)

  def xmlTextEscape(s: String): String =
    s.replace("<", "&lt;")
     .replace("&", "&amp;")
}