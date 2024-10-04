package libretto.lambda.examples.workflow.generic.vis

import java.nio.file.{Paths, Files}
import java.nio.charset.StandardCharsets
import libretto.lambda.util.NonEmptyList

import Px.*

case class SVGDocument(contentElem: SVGElem) {
  import SVGDocument.*

  def writeTo(fileName: String, width: Int, height: Int): Unit = {
    val fullXmlString =
      s"""<svg xmlns="http://www.w3.org/2000/svg" width="$width" height="$height">
         |$SCRIPT
         |<g id="content">
         |${contentElem.xmlString}
         |</g>
         |</svg>
         """.stripMargin
    val bytes = fullXmlString.getBytes(StandardCharsets.UTF_8)
    val path = Paths.get(fileName)
    Files.write(path, bytes)
  }

}

object SVGDocument {
  private[SVGDocument] val SCRIPT =
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

sealed trait SVGNode {
  def xmlString: String
}

object SVGNode {
  case class TextContent(value: String) extends SVGNode {
    override def xmlString: String =
      SVG.xmlTextEscape(value)
  }

  case class Comment(text: String) extends SVGNode {
    require(!text.contains("--"), "Silly rule that XML comments may not contain double hyphen (--)")

    override def xmlString: String =
      s"<!-- $text -->"

  }
}

/** Representation of a _subset_ of SVG. */
sealed trait SVGElem extends SVGNode {
  import SVG.*
  import SVGElem.*

  def xmlTag: String
  def xmlAttributes: Map[String, String]
  def xmlContent: List[SVGNode]

  override def xmlString: String =
    val content: Option[String] = xmlContent match
      case Nil                  => None
      case elems: List[SVGNode] => Some(elems.map(_.xmlString).mkString("\n", "\n", "\n"))
    s"<$xmlTag"
      + xmlAttributes
        .map { case (k, v) => s"$k=\"$v\"" }
        .mkString(" ", " ", "")
      + content.fold("/>")(str => s">$str</$xmlTag>")

  def translate(dx: Double, dy: Double): SVGElem =
    transform(Transform.Translate(dx, dy))

  def scale(s: Double): SVGElem =
    scale(s, s)

  def scale(sx: Double, sy: Double): SVGElem =
    transform(Transform.Scale(sx, sy))

  def transform(t: Transform): SVGElem =
    this match
      case Transformed(obj, ts) => Transformed(obj, t :: ts)
      case obj: ElemProper      => Transformed(obj, t)
}

object SVGElem {
  import SVG.*

  /* An auxiliary node for Scala representation.
   * In xml and DOM, transform is represented as an attribute on another element. */
  case class Transformed(obj: ElemProper, transforms: NonEmptyList[Transform]) extends SVGElem:
    override def xmlTag = obj.xmlTag

    override lazy val xmlAttributes =
      obj.xmlAttributes.updated("transform", transforms.map(_.attributeValue).toList.mkString(" "))

    override def xmlContent = obj.xmlContent
  end Transformed

  object Transformed:
    def apply(obj: ElemProper, t: Transform): Transformed =
      Transformed(obj, NonEmptyList.of(t))

  sealed trait ElemProper extends SVGElem

  case class Group(children: List[SVGNode]) extends ElemProper:
    override def xmlTag = "g"
    override def xmlAttributes = Map.empty[String, String]
    override def xmlContent = children

  object Group:
    def apply(children: SVGNode*): Group =
      Group(children.toList)

  case class Text(
    value: String,
    x: Px,
    y: Px,
    fontFamily: FontFamily,
    fontSize: Px,
    textAnchor: TextAnchor = TextAnchor.Start,
  ) extends ElemProper :
    import Px.*

    override def xmlTag =
      "text"

    override def xmlAttributes =
      Map(
        "x" -> String.valueOf(x.pixels),
        "y" -> String.valueOf(y.pixels),
        "style" -> s"font-family: ${fontFamily.cssValue}; font-size: ${fontSize.pixels}px",
        "text-anchor" -> textAnchor.cssValue,
      )

    override def xmlContent =
      List(SVGNode.TextContent(value))

  case class Rect(
    x: Px,
    y: Px,
    w: Px,
    h: Px,
    fill: Option[Color],
    stroke: Option[Stroke],
    clipPath: Option[ClipPath],
    rx: Option[Double] = None,
    ry: Option[Double] = None,
  ) extends ElemProper {
    override def xmlTag: String = "rect"

    override def xmlContent: List[SVGNode] = Nil

    override def xmlAttributes: Map[String, String] =
      Map(
        "x" -> s"${x.pixels}",
        "y" -> s"${y.pixels}",
        "width" -> s"${w.pixels}",
        "height" -> s"${h.pixels}",
        "fill" -> fill.fold("none")(_.cssValue),
      ) ++ (stroke match
        case None =>
          List("stroke" -> "none")
        case Some(Stroke(width, color)) =>
          List(
            "stroke" -> color.cssValue,
            "stroke-width" -> s"$width",
          )
      ) ++ clipPath.map(p => "clip-path" -> p.cssValue)
        ++ rx.map(rx => "rx" -> rx.toString)
        ++ ry.map(ry => "ry" -> ry.toString)
  }

  object Rect {
    def solid(w: Px, h: Px, color: Color): Rect =
      Rect(0.px, 0.px, w, h, fill = Some(color), stroke = None, clipPath = None)

    def outlineInner(w: Px, h: Px, thickness: Double, color: Color): Rect =
      val strokeWidth = thickness * 2 // the outer half will be clipped
      Rect(0.px, 0.px, w, h, fill = None, stroke = Some(Stroke(strokeWidth, color)), Some(ClipPath.FillBox))
  }

  case class Circle(radius: Px, fill: Option[Color], stroke: Option[Stroke]) extends ElemProper {
    override def xmlTag: String = "circle"
    override def xmlContent: List[SVGNode] = Nil

    override def xmlAttributes: Map[String, String] =
      Map(
        "cx" -> "0",
        "cy" -> "0",
        "r" -> s"${radius.pixels}",
        "fill" -> fill.fold("none")(_.cssValue),
      ) ++ (stroke match
        case None =>
          List("stroke" -> "none")
        case Some(Stroke(width, color)) =>
          List(
            "stroke" -> color.cssValue,
            "stroke-width" -> s"$width",
          )
      )
  }

  case class Path(cmds: Path.Command*) extends ElemProper {
    override def xmlTag: String = "path"

    override def xmlContent: List[SVGNode] = Nil

    override def xmlAttributes: Map[String, String] =
      Map(
        "d" -> cmds.map(_.stringValue).mkString(" "),
        "fill" -> "black",
        "stroke" -> "none",
      )
  }

  object Path {
    enum Command:
      case MoveTo(x: Px, y: Px)
      case LineTo(x: Px, y: Px)
      case CurveTo(c1x: Px | Double, c1y: Px | Double, c2x: Px | Double, c2y: Px | Double, tgtX: Px, tgtY: Px)
      case Close

      def stringValue: String =
        this match
          case MoveTo(x, y) => s"M $x $y"
          case LineTo(x, y) => s"L $x $y"
          case CurveTo(c1x, c1y, c2x, c2y, tgtX, tgtY) => s"C $c1x $c1y, $c2x $c2y, $tgtX $tgtY"
          case Close => "Z"
  }
}

object SVG {
  enum Transform:
    case Scale(sx: Double, sy: Double)
    case Translate(dx: Double, dy: Double)

    def attributeValue: String =
      this match
        case Scale(sx, sy) => s"scale($sx $sy)"
        case Translate(dx, dy) => s"translate($dx $dy)"

  enum FontFamily:
    case Monospace
    case Serif
    case SansSerif

    def cssValue: String =
      this match
        case Monospace => "monospace"
        case Serif => "serif"
        case SansSerif => "sans-serif"

  enum TextAnchor:
    case Start
    case Middle
    case End

    def cssValue: String =
      this match
        case Start => "start"
        case Middle => "middle"
        case End => "end"

  extension (c: Color) {
    def cssValue: String =
      import Color.*
      c match
        case Black => "black"
        case White => "white"
        case Red => "red"
        case RGB(r, g, b) => s"rgb($r, $g, $b)"
  }

  case class Stroke(width: Double, color: Color)

  enum ClipPath:
    case FillBox

    def cssValue: String =
      this match
        case FillBox =>  "fill-box"

  def xmlTextEscape(s: String): String =
    s.replace("<", "&lt;")
     .replace("&", "&amp;")
}