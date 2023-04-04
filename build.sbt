
lazy val commonSettings = Seq(
    name                 := "Princess",
    organization         := "uuverifiers",
    version              := "2023-04-07",
    homepage             := Some(url("https://philipp.ruemmer.org/princess.shtml")),
    licenses             := Seq("BSD-3-Clause" -> url("https://opensource.org/licenses/BSD-3-Clause")),
    scmInfo              := Some(ScmInfo(
                                   url("https://github.com/uuverifiers/princess"),
                                   "scm:git@github.com/uuverifiers/princess.git")),
    developers           := List(
                              Developer(
                                id    = "p_ruemmer",
                                name  = "Philipp Ruemmer",
                                email = "ph_r@gmx.net",
                                url   = url("https://philipp.ruemmer.org")
                              ),
                              Developer(
                                id    = "zafer.esen",
                                name  = "Zafer Esen",
                                email = "zafer.esen@it.uu.se",
                                url   = url("https://katalog.uu.se/empinfo/?id=N18-2424")
                              ),
                              Developer(
                                id    = "angelo.brillout",
                                name  = "Angelo Brillout",
                                email = "angelo.brillout@gmail.com",
                                url   = url("https://ch.linkedin.com/in/angelo-brillout-2942bb7")
                              ),
                              Developer(
                                id    = "peter.backeman",
                                name  = "Peter Backeman",
                                email = "peter@backeman.se",
                                url   = url("http://www.es.mdh.se/staff/4393-Peter__Backeman")
                              ),
                              Developer(
                                id    = "peter.baumgartner",
                                name  = "Peter Baumgartner",
                                email = "Peter.Baumgartner@data61.csiro.au",
                                url   = url("http://users.cecs.anu.edu.au/~baumgart/")
                              ),
                              Developer(
                                id    = "amanda.stjerna",
                                name  = "Amanda Stjerna",
                                email = "mail@amandastjerna.se",
                                url   = url("https://amandastjerna.se/")
                              )
                            ),
    description          := "Princess is a theorem prover (aka SMT Solver) for Presburger arithmetic, uninterpreted predicates, and various other theories.",
    scalaVersion         := "2.11.12",
    crossScalaVersions   := Seq("2.11.12", "2.12.17"),
    fork in run          := true,
    cancelable in Global := true,
    publishTo := Some(Resolver.file("file", new File( "/tmp/shared-repo" )) )
)

////////////////////////////////////////////////////////////////////////////////
// Jar files for the parsers

lazy val parserSettings = Seq(
//    publishArtifact in packageDoc := false,
//    publishArtifact in packageSrc := false,
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
      case "2.12.17" => "-opt:_"
    }}).value,
//
    libraryDependencies +=
      "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.4",
//
    libraryDependencies +=
      "net.sf.squirrel-sql.thirdparty-non-maven" % "java-cup" % "0.11a")
