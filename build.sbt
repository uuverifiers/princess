
lazy val commonSettings = Seq(
    name := "Princess",
    organization := "uuverifiers",
    version := "2016-07-01",
    scalaVersion := "2.11.8"
)

// Jar files for the parsers

lazy val parserSettings = Seq(
    publishArtifact in packageDoc := false,
    publishArtifact in packageSrc := false,
    exportJars := true,
    crossPaths := true 
)

lazy val parser = (project in file("parser")).
  settings(commonSettings: _*).
  settings(parserSettings: _*).
  settings(
    name := "Princess-parser",
    packageBin in Compile := baseDirectory.value / "parser.jar"
  )

lazy val smtParser = (project in file("smt-parser")).
  settings(commonSettings: _*).
  settings(parserSettings: _*).
  settings(
    name := "Princess-smt-parser",
    packageBin in Compile := baseDirectory.value / "smt-parser.jar"
  )

// Actual project

lazy val root = (project in file(".")).
  aggregate(parser, smtParser).
  dependsOn(parser, smtParser).
  settings(commonSettings: _*).
//
  settings(
    scalaSource in Compile := baseDirectory.value / "src",
//
    mainClass in Compile := Some("ap.CmdlMain"),
//
    scalacOptions in Compile ++=
      List("-optimise",
           "-feature",
           "-language:implicitConversions,postfixOps,reflectiveCalls"),
//
    libraryDependencies +=
      "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.4",
//
    libraryDependencies +=
      "net.sf.squirrel-sql.thirdparty-non-maven" % "java-cup" % "0.11a")
