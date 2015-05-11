lazy val root = (project in file(".")).
  settings(
    name := "BREU"
  )


libraryDependencies += "org.scalatest" % "scalatest_2.10" % "2.0" % "test"

libraryDependencies += "io.argonaut" %% "argonaut" % "6.0.4" 
