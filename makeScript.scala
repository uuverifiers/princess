object genCopy {
  def main(args : Array[String]) = {
    val lines = scala.io.Source.fromFile(args(0)).getLines
    for (l <- lines) {
      val outFile = l.split('/').tail.mkString("")
      println("timeout 300s ./princess -connection=strong +assert TPTP-v7.0.0/Problems/" + l + " > out/" + outFile + " 2>&1")
    }
  }
}
