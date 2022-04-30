resolvers += Resolver.mavenCentral

ThisBuild / scalaVersion := "3.1.2"

ThisBuild / organization := "com.github.tomasmikula"

ThisBuild / licenses += ("MPL 2.0", url("https://opensource.org/licenses/MPL-2.0"))
ThisBuild / homepage := Some(url("https://github.com/TomasMikula/libretto"))
ThisBuild / scmInfo := Some(
  ScmInfo(
    url("https://github.com/TomasMikula/libretto"),
    "scm:git:git@github.com:TomasMikula/libretto.git"
  )
)

ThisBuild / publishTo := {
  val nexus = "https://oss.sonatype.org/"
  if (isSnapshot.value)
    Some("snapshots" at nexus + "content/repositories/snapshots")
  else
    Some("releases"  at nexus + "service/local/staging/deploy/maven2")
}

ThisBuild / pomExtra := (
  <developers>
    <developer>
      <id>TomasMikula</id>
      <name>Tomas Mikula</name>
      <url>http://github.com/TomasMikula/</url>
    </developer>
  </developers>
)

import ReleaseTransformations._

releaseProcess := Seq[ReleaseStep](
  checkSnapshotDependencies,
  inquireVersions,
  runClean,
  runTest,
  setReleaseVersion,
  commitReleaseVersion,
  tagRelease,
  releaseStepCommand("publishSigned"),
  releaseStepCommand("sonatypeRelease"),
  setNextVersion,
  commitNextVersion,
  pushChanges,
)

lazy val core = project
  .in(file("core"))
  .settings(
    name := "libretto",
    scalacOptions ++= Seq(
      "-deprecation",
      "-Ykind-projector", // support '*' as a placeholder in type lambdas
    ),
  )

lazy val testing = project
  .in(file("testing"))
  .dependsOn(core)
  .settings(
    name := "libretto-testing",
    libraryDependencies ++= Seq(
      "org.scalatest" %% "scalatest" % "3.2.9",
    ),
  )

lazy val coreTests = project
  .in(file("core-tests"))
  .dependsOn(core, testing)
  .settings(
    name := "core-tests",
    publish / skip := true,
  )

lazy val examples = project
  .in(file("examples"))
  .dependsOn(core, testing)
  .settings(
    name := "libretto-examples",
  )

lazy val root = project
  .in(file("."))
  .settings(
    publish / skip := true,
  )
  .aggregate(
    core,
    testing,
    coreTests,
    examples,
  )

lazy val laikaSite         = taskKey[File]("generates HTML from Markdown using Laika")
lazy val docsSite          = taskKey[File]("generates doc site")
lazy val prepareDocsLatest = taskKey[File]("generates doc site to the publishing directory (docs/latest)")
lazy val commitDocsLatest  = taskKey[Unit]("generates and commits the current docs")

lazy val docs = project
  .in(file("docs-project")) // must not be the same as mdocIn
  .dependsOn(core)
  .enablePlugins(MdocPlugin)
  .settings(
    scalacOptions += "-Ykind-projector", // so that we can use '*' placeholder in the tutorial
    mdocIn := file("tutorial"),
    mdocVariables := Map(
      "SCALA_VERSION" -> (ThisBuild / scalaVersion).value,
    ),
    laikaSite := {
      import cats.effect.IO
      import cats.effect.unsafe.implicits.global
      import laika.api.Transformer
      import laika.format.{HTML, Markdown}
      import laika.helium.Helium
      import laika.helium.config.TextLink
      import laika.io.implicits._
      import laika.markdown.github.GitHubFlavor
      import laika.parse.code.SyntaxHighlighting
      import laika.theme.Theme

      // add a dependency on mdoc
      mdoc.toTask("").value
      val srcDir = mdocOut.value
      val tgtDir = target.value / "laika-site"

      Transformer
        .from(Markdown)
        .to(HTML)
        .withRawContent // support html content in input markdown documents
        .using(GitHubFlavor, SyntaxHighlighting)
        .parallel[IO]
        .withTheme(
          Helium.defaults
            .site.topNavigationBar(
              homeLink = TextLink.external("https://github.com/TomasMikula/libretto", "GitHub"),
            )
            // Change the code font, since Helium's default "Fira Code" lacks some symbols used in tutorial
            // and the fallback font is not monospace. See https://github.com/planet42/Laika/issues/218.
            .all.fontFamilies(
              body = "Lato",      // just repeating the default
              headlines = "Lato", // just repeating the default
              code = "Menlo",
            )
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

      tgtDir
    },
    docsSite := {
      val scaladocDir  = (core / Compile / doc).value
      val laikaSiteDir = laikaSite.value

      val outputDir = target.value / "docs-site"

      IO.delete(outputDir)
      IO.copyDirectory(scaladocDir,  outputDir / "scaladoc")
      IO.copyDirectory(laikaSiteDir, outputDir / "tutorial")

      outputDir
    },
    prepareDocsLatest := {
      val baseDir = (root / baseDirectory).value
      val srcDir = docsSite.value
      val tgtDir = baseDir / "docs" / "latest"

      val git = sbtrelease.Git.mkVcs(baseDir)

      git.cmd("rm", "-rf", "--ignore-unmatch", tgtDir) ! ;
      IO.copyDirectory(srcDir, tgtDir)
      git.cmd("add", tgtDir) ! ;

      tgtDir
    },
    commitDocsLatest := {
      val latestDocsDir = prepareDocsLatest.value

      val git = sbtrelease.Git.mkVcs((root / baseDirectory).value)

      streams.value.log.info(s"Commiting latest docs in $latestDocsDir")
      git.cmd("commit", "-m", "Publish latest docs.", latestDocsDir) ! ;
    },
  )
