resolvers += Resolver.mavenCentral

ThisBuild / scalaVersion := "3.2.1"

ThisBuild / organization := "dev.continuously"

ThisBuild / licenses += ("MPL 2.0", url("https://opensource.org/licenses/MPL-2.0"))
ThisBuild / homepage := Some(url("https://github.com/TomasMikula/libretto"))
ThisBuild / scmInfo := Some(
  ScmInfo(
    url("https://github.com/TomasMikula/libretto"),
    "scm:git:git@github.com:TomasMikula/libretto.git"
  )
)

ThisBuild / sonatypeCredentialHost := "s01.oss.sonatype.org"
ThisBuild / publishTo := sonatypePublishTo.value

ThisBuild / pomExtra := (
  <developers>
    <developer>
      <id>TomasMikula</id>
      <name>Tomas Mikula</name>
      <url>https://continuously.dev</url>
    </developer>
  </developers>
)

// o - write results back to sbt
// D - show all durations
// S - show short stack traces
ThisBuild / Test / testOptions += Tests.Argument(TestFrameworks.ScalaTest, "-oDS")

// don't wait for all tests of a file before reporting
ThisBuild / Test / logBuffered := false

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

val ZioVersion = "2.0.3"

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
  )

lazy val testingScalatest = project
  .in(file("testing-scalatest"))
  .dependsOn(core, testing)
  .settings(
    name := "libretto-testing-scalatest",
    libraryDependencies ++= Seq(
      "org.scalatest" %% "scalatest" % "3.2.15",
    ),
  )

lazy val coreTests = project
  .in(file("core-tests"))
  .dependsOn(core, testing, testingScalatest)
  .settings(
    name := "core-tests",
    publish / skip := true,
  )

lazy val examples = project
  .in(file("examples"))
  .dependsOn(core, testing, testingScalatest)
  .settings(
    name := "libretto-examples",
  )

lazy val mashup = project
  .in(file("mashup"))
  .dependsOn(core)
  .settings(
    name := "libretto-mashup",
    publish / skip := true, // experimental project, do not publish
    libraryDependencies ++= Seq(
      "dev.zio" %% "zio" % ZioVersion,
      "dev.zio" %% "zio-json" % "0.3.0",
      "io.d11" %% "zhttp" % "2.0.0-RC11",
    ),
  )

lazy val mashupExamples = project
  .in(file("mashup-examples"))
  .dependsOn(mashup)
  .settings(
    name := "libretto-mashup-examples",
    fork := true,
    publish / skip := true, // experimental project, do not publish
  )

lazy val librettoZio = project
  .in(file("libretto-zio"))
  .dependsOn(
    core,
    examples % Test,
  )
  .settings(
    name := "libretto-zio",
    libraryDependencies ++= Seq(
      "dev.zio" %% "zio"          % ZioVersion,
      "dev.zio" %% "zio-streams"  % ZioVersion,
      "dev.zio" %% "zio-test"     % ZioVersion % Test,
      "dev.zio" %% "zio-test-sbt" % ZioVersion % Test,
    ),
    testFrameworks += new TestFramework("zio.test.sbt.ZTestFramework"),
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
    mashup,
    mashupExamples,
    librettoZio,
  )

lazy val laikaSite         = taskKey[File]("generates HTML from Markdown using Laika")
lazy val docsSite          = taskKey[File]("generates doc site")

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
  )
