lazy val root = (project in file(".")).
  settings(
    name := "Princess",
    version := "2016-07-01",
//
    scalaVersion := "2.11.8",
    scalaSource in Compile := baseDirectory.value / "src",
//
    mainClass in Compile := Some("ap.CmdlMain"),
//
    scalacOptions in Compile ++=
      List("-optimise",
           "-feature",
           "-language:implicitConversions,postfixOps,reflectiveCalls"),
//
    unmanagedJars in Compile <++= baseDirectory map { base =>
        val baseDirectories = (base / "parser") +++ (base / "smt-parser")
        val customJars = (baseDirectories ** "*.jar")
        customJars.classpath
    },
//
    libraryDependencies +=
      "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.4",
//
    libraryDependencies +=
      "net.sf.squirrel-sql.thirdparty-non-maven" % "java-cup" % "0.11a"
)



