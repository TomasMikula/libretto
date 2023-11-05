import cats.effect.IO
import cats.effect.unsafe.implicits.global
import laika.api.Transformer
import laika.config.SyntaxHighlighting
import laika.format.{HTML, Markdown}
import laika.format.Markdown.GitHubFlavor
import laika.helium.Helium
import laika.helium.config.TextLink
import laika.io.syntax._
import laika.theme.Theme

object LaikaMarkdownToHtml {

  def apply(srcDir: String, tgtDir: String): Unit = {
    Transformer
      .from(Markdown)
      .to(HTML)
      .withRawContent // support html content in input markdown documents
      .using(GitHubFlavor)
      .using(SyntaxHighlighting)
      .parallel[IO]
      .withTheme(
        Helium.defaults
          .site.topNavigationBar(
            homeLink = TextLink.external("https://github.com/TomasMikula/libretto", "GitHub"),
          )
          .site.addFontResources(/* Empty overrides Default! We use our custom CSS for the fonts. */)
          .build
      )
      .build
      .use { transformer =>
        transformer
          .fromDirectory(srcDir)
          .toDirectory(tgtDir)
          .transform
      }
      .unsafeRunSync()
  }
}
