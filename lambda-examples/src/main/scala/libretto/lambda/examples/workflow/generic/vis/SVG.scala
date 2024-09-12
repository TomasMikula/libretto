package libretto.lambda.examples.workflow.generic.vis

import java.nio.file.{Paths, Files}
import java.nio.charset.StandardCharsets
import libretto.lambda.util.NonEmptyList

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
        .mkString(" ", " ", "")
      + content.fold("/>")(str => s">$str</$xmlTag>")

  def writeTo(fileName: String): Unit =
    val fullXmlString =
      s"""<svg xmlns="http://www.w3.org/2000/svg">
         |$SCRIPT
         |<g id="content">
         |$xmlString
         |</g>
         |</svg>
         """.stripMargin
    val bytes = fullXmlString.getBytes(StandardCharsets.UTF_8)
    val path = Paths.get(fileName)
    Files.write(path, bytes)

  def translate(dx: Double, dy: Double): SVG =
    transform(Transform.Translate(dx, dy))

  def scale(s: Double): SVG =
    println(s"scaling by $s")
    transform(Transform.Scale(s))

  def transform(t: Transform): SVG =
    this match
      case Transformed(obj, ts) => Transformed(obj, t :: ts)
      case obj: Proper          => Transformed(obj, t)
}

object SVG {
  /* An auxiliary node for Scala representation.
   * In xml and DOM, transform is represented as an attribute on another element. */
  case class Transformed(obj: SVG.Proper, transforms: NonEmptyList[Transform]) extends SVG:
    override def xmlTag = obj.xmlTag

    override lazy val xmlAttributes =
      obj.xmlAttributes.updated("transform", transforms.map(_.attributeValue).toList.mkString(" "))

    override def xmlContent = obj.xmlContent
  end Transformed

  object Transformed:
    def apply(obj: SVG.Proper, t: Transform): Transformed =
      Transformed(obj, NonEmptyList.of(t))

  sealed trait Proper extends SVG

  case class Group(children: List[SVG]) extends Proper:
    override def xmlTag = "g"
    override def xmlAttributes = Map.empty[String, String]
    override def xmlContent = children

  object Group:
    def apply(children: SVG*): Group =
      Group(children.toList)

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
    case Translate(dx: Double, dy: Double)

    def attributeValue: String =
      this match
        case Scale(value) => s"scale($value)"
        case Translate(dx, dy) => s"translate($dx $dy)"

  enum FontFamily:
    case Monospace

    def cssValue: String =
      this match
        case Monospace => "monospace"

  opaque type Px = Int
  object Px {
    def apply(n: Int): Px =
      require(n >= 0)
      n

    extension (x: Px)
      def pixels: Int = x
      def *(k: Int): Px = Px(x * k)
  }

  extension (n: Int)
    def px: Px = Px(n)

  def xmlTextEscape(s: String): String =
    s.replace("<", "&lt;")
     .replace("&", "&amp;")

  private[SVG] val SCRIPT =
    """<script>
    |// <![CDATA[
    |
    |window.onload = function() {
    |  var svg = document.rootElement
    |  var content = document.getElementById("content");
    |
    |  var scaleTransform = svg.createSVGTransform();
    |  var translateTransform = svg.createSVGTransform();
    |  content.transform.baseVal.appendItem(translateTransform);
    |  content.transform.baseVal.appendItem(scaleTransform);
    |
    |  var scale = 1.0;
    |  var tx = 0;
    |  var ty = 0;
    |  svg.onwheel = function(evt) {
    |    console.log(evt);
    |    var x = evt.offsetX
    |    var y = evt.offsetY
    |
    |    var ds = Math.pow(1.01, evt.deltaY)
    |
    |    console.log("x="+x+" y="+y);
    |    console.log("old: scale=" + scale + " tx=" + tx + " ty=" + ty);
    |    tx = x - ds * (x - tx);
    |    ty = y - ds * (y - ty);
    |    scale = ds * scale;
    |    console.log("new: scale=" + scale + " tx=" + tx + " ty=" + ty);
    |
    |    scaleTransform.setScale(scale, scale);
    |    translateTransform.setTranslate(tx, ty);
    |  }
    |}
    |
    |// ]]>
    |</script>
    """.stripMargin
}