resolvers += Resolver.mavenCentral

ThisBuild / scalaVersion := "3.6.3"

ThisBuild / organization := "dev.continuously.libretto"

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
// F - show full stack traces
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
  releaseStepCommand("sonatypeReleaseAll dev.continuously"),
  setNextVersion,
  commitNextVersion,
  pushChanges,
)

val ScalatestVersion = "3.2.16"
val ZioVersion = "2.1.16"
val ZioJsonVersion = "0.7.39"
val ZioHttpVersion = "3.0.1"

val commonScalacOptions =
  Seq(
    "-deprecation",
    "-Xkind-projector:underscores",
  )

lazy val lambda = crossProject(JVMPlatform, JSPlatform)
  .in(file("lambda"))
  .settings(
    name := "libretto-lambda",
    scalacOptions ++= commonScalacOptions,
    libraryDependencies ++= Seq(
      "org.scalatest" %%% "scalatest" % ScalatestVersion % Test,
    ),
  )

lazy val lambdaExamples = project
  .in(file("lambda-examples"))
  .dependsOn(
    lambda.jvm,
  )
  .settings(
    name := "libretto-lambda-examples",
    publish / skip := true, // experimental project, do not publish
    scalacOptions ++= commonScalacOptions,
    libraryDependencies ++= Seq(
      "org.scalatest" %% "scalatest" % ScalatestVersion % Test,
    ),
    fork := true,
  )

lazy val core = project
  .in(file("core"))
  .dependsOn(lambda.jvm)
  .settings(
    name := "libretto-core",
    scalacOptions ++= commonScalacOptions,
  )

lazy val testing = project
  .in(file("testing"))
  .dependsOn(core)
  .settings(
    name := "libretto-testing",
    scalacOptions ++= commonScalacOptions,
  )

lazy val testingScalatest = project
  .in(file("testing-scalatest"))
  .dependsOn(core, testing)
  .settings(
    name := "libretto-testing-scalatest",
    scalacOptions ++= commonScalacOptions,
    libraryDependencies ++= Seq(
      "org.scalatest" %% "scalatest" % ScalatestVersion,
    ),
  )

lazy val coreTests = project
  .in(file("core-tests"))
  .dependsOn(testingScalatest % "test->compile")
  .settings(
    name := "core-tests",
    scalacOptions ++= commonScalacOptions,
    publish / skip := true,
  )

lazy val stream = project
  .in(file("stream"))
  .dependsOn(
    core,
    testingScalatest % "test->compile",
  )
  .settings(
    name := "libretto-stream",
    scalacOptions ++= commonScalacOptions,
  )

lazy val examples = project
  .in(file("examples"))
  .dependsOn(
    core,
    stream,
    testingScalatest % "test->compile",
  )
  .settings(
    name := "libretto-examples",
    scalacOptions ++= commonScalacOptions,
  )

lazy val mashup = project
  .in(file("mashup"))
  .dependsOn(core)
  .settings(
    name := "libretto-mashup",
    publish / skip := true, // experimental project, do not publish
    scalacOptions ++= commonScalacOptions,
    libraryDependencies ++= Seq(
      "dev.zio" %% "zio" % ZioVersion,
      "dev.zio" %% "zio-json" % ZioJsonVersion,
      "dev.zio" %% "zio-http" % ZioHttpVersion,
    ),
  )

lazy val mashupExamples = project
  .in(file("mashup-examples"))
  .dependsOn(mashup, testingScalatest)
  .settings(
    name := "libretto-mashup-examples",
    scalacOptions ++= commonScalacOptions,
    fork := true,
    publish / skip := true, // experimental project, do not publish
  )

lazy val librettoZio = project
  .in(file("libretto-zio"))
  .dependsOn(
    core,
    stream,
    examples % Test,
  )
  .settings(
    name := "libretto-zio",
    scalacOptions ++= commonScalacOptions,
    libraryDependencies ++= Seq(
      "dev.zio" %% "zio"          % ZioVersion,
      "dev.zio" %% "zio-streams"  % ZioVersion,
      "dev.zio" %% "zio-test"     % ZioVersion % Test,
      "dev.zio" %% "zio-test-sbt" % ZioVersion % Test,
    ),
    testFrameworks += new TestFramework("zio.test.sbt.ZTestFramework"),
  )

lazy val typology = project
  .in(file("typology"))
  .dependsOn(
    core,
    testingScalatest % "test->compile",
  )
  .settings(
    name := "libretto-typology",
    publish / skip := true, // experimental project, do not publish
    scalacOptions ++= commonScalacOptions,
    fork := true,
  )

lazy val kindville = crossProject(JVMPlatform, JSPlatform)
  .in(file("kindville"))
  .settings(
    name := "kindville",
    publish / skip := true, // experimental project, do not publish
    scalacOptions ++= commonScalacOptions ++ Seq("-explain", "-Xcheck-macros"),
    libraryDependencies ++= Seq(
      "org.scalatest" %%% "scalatest" % ScalatestVersion % Test,
    ),
  )

lazy val root = project
  .in(file("."))
  .settings(
    publish / skip := true,
  )
  .aggregate(
    lambda.jvm,
    lambda.js,
    lambdaExamples,
    core,
    testing,
    coreTests,
    stream,
    examples,
    mashup,
    mashupExamples,
    librettoZio,
    typology,
    kindville.jvm,
    kindville.js,
  )

lazy val laikaSite         = taskKey[File]("generates HTML from Markdown using Laika")
lazy val docsSite          = taskKey[File]("generates doc site")

lazy val docs = project
  .in(file("docs-project")) // must not be the same as mdocIn
  .dependsOn(core)
  .enablePlugins(MdocPlugin)
  .settings(
    scalacOptions ++= commonScalacOptions,
    mdocIn := file("tutorial"),
    mdocVariables := Map(
      "SCALA_VERSION" -> (ThisBuild / scalaVersion).value,
    ),
    laikaSite := {
      // add a dependency on mdoc
      mdoc.toTask("").value

      val srcDir = mdocOut.value
      val tgtDir = target.value / "laika-site"

      LaikaMarkdownToHtml(srcDir.absolutePath, tgtDir.absolutePath)

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
