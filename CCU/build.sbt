lazy val root = (project in file(".")).
  settings(
    name := "BREU"
  )


// addSbtPlugin("com.eed3si9n" % "sbt-assembly" % "0.13.0")
assemblyOption in assembly := (assemblyOption in assembly).value.copy(includeScala = false)

scalaVersion := "2.11.6"

// libraryDependencies += "org.scalaz" %% "scalaz-core" % "7.1.3"
// libraryDependencies += "io.argonaut" %% "argonaut" % "6.0.4" 


