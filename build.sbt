scalaVersion := "3.0.0-M2"

lazy val libretto = project
//  .settings(...)

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
