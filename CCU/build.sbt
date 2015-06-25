lazy val root = (project in file(".")).
  settings(
    name := "BREU"
  )

scalaVersion := "2.11.6"

libraryDependencies += "io.argonaut" %% "argonaut" % "6.0.4" 
