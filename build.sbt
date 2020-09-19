scalaVersion := "2.13.2"

addCompilerPlugin("org.typelevel" % "kind-projector" % "0.11.0" cross CrossVersion.full)

scalacOptions ++= Seq(
  "-deprecation",
)