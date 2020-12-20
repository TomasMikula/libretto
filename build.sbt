scalaVersion := "3.0.0-M2"

resolvers += Resolver.mavenCentral

lazy val libretto = project
  .in(file("."))
  .settings(
    libraryDependencies ++= Seq(
      "org.scalatest" %% "scalatest" % "3.2.3" % "test",
    ),
  )

// to compile documentation, run `sbt docs/mdoc`
lazy val docs = project
  .in(file("docs-project"))
  .dependsOn(libretto)
  .enablePlugins(MdocPlugin)
  .settings(
    mdocIn := file("mdoc-src"),
    mdocOut := file("docs"),
  )

scalacOptions ++= Seq(
  "-deprecation",
  "-Ykind-projector", // support '*' as a placeholder in type lambdas
)
