scalaVersion := "2.13.4"

addCompilerPlugin("org.typelevel" % "kind-projector" % "0.11.2" cross CrossVersion.full)

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
)
