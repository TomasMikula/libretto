resolvers += Resolver.mavenCentral

ThisBuild / scalaVersion := "3.0.1"

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
    libraryDependencies ++= Seq(
      "org.scalatest" %% "scalatest" % "3.2.9" % "test",
    ),
  )

lazy val examples = project
  .in(file("examples"))
  .dependsOn(core)
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
    examples,
  )
