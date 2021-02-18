resolvers += Resolver.mavenCentral

val scalaVersionString = "3.0.0-RC1"

lazy val core = project
  .in(file("core"))
  .settings(
    scalaVersion := scalaVersionString,
    scalacOptions ++= Seq(
      "-deprecation",
      "-Ykind-projector", // support '*' as a placeholder in type lambdas
    ),
    libraryDependencies ++= Seq(
      "org.scalatest" %% "scalatest" % "3.2.4" % "test",
    ),
  )

lazy val examples = project
  .in(file("examples"))
  .dependsOn(core)
  .settings(
    scalaVersion := scalaVersionString,
  )
