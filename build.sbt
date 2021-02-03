resolvers += Resolver.mavenCentral

lazy val core = project
  .in(file("core"))
  .settings(
    scalaVersion := "3.0.0-M3",
    scalacOptions ++= Seq(
      "-deprecation",
      "-Ykind-projector", // support '*' as a placeholder in type lambdas
    ),
    libraryDependencies ++= Seq(
      "org.scalatest" %% "scalatest" % "3.2.3" % "test",
    ),
  )

// to compile documentation, run `sbt docs/mdoc`
lazy val docs = project
  .in(file("docs-project"))
  .dependsOn(core)
  .enablePlugins(MdocPlugin)
  .settings(
    mdocIn := file("mdoc-src"),
    mdocOut := file("docs"),
  )
