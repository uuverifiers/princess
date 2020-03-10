
lazy val commonSettings = Seq(
    name := "Princess",
    organization := "uuverifiers",
    version := "unstable-SNAPSHOT",
    scalaVersion := "2.11.12",
    crossScalaVersions := Seq("2.11.12", "2.12.10"),
    fork in run := true,
    cancelable in Global := true,
    publishTo := Some(Resolver.file("file",  new File( "/tmp/shared-repo" )) )
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
  ).
  disablePlugins(AssemblyPlugin)

lazy val smtParser = (project in file("smt-parser")).
  settings(commonSettings: _*).
  settings(parserSettings: _*).
  settings(
    name := "Princess-smt-parser",
    packageBin in Compile := baseDirectory.value / "smt-parser.jar"
  ).
  disablePlugins(AssemblyPlugin)

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
      List("-feature",
           "-language:implicitConversions,postfixOps,reflectiveCalls"),
    scalacOptions += (scalaVersion map { sv => sv match {
      case "2.11.12" => "-optimise"
      case "2.12.10" => "-opt:_"
    }}).value,
//
    libraryDependencies +=
      "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.4",
//
    libraryDependencies +=
      "net.sf.squirrel-sql.thirdparty-non-maven" % "java-cup" % "0.11a")
