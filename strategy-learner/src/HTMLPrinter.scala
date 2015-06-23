import java.io.{File, FilenameFilter}


object HTMLPrinter extends App {

  import Status._

  val baseDir = "/home/ptr/Princess/unification-modulo/strategy-learner/src/"
  val logFileDir = new File(baseDir + "logs/")
  val benchmarkDir = baseDir + "benchmarks/"
  val benchFile  = new File(baseDir + "bench.list")

  val logResults = Console.withOut(Console.err) {  
    println("Reading " + logFileDir + " ...")

      (for (logFile <- logFileDir.listFiles;
            if (logFile.getName matches """[0-9]+\.log""");
            val conts = (new LogReader(logFile)).results;
            version = (logFile.getName stripSuffix ".log").toInt)
       yield (version -> conts)).toMap
  }


  val allVersions =
    logResults.keys.toSeq.sortBy(x => -x)

  println("<html>")
  println("<head>")
  println("  <meta http-equiv=\"content-type\"")
  println(" content=\"text/html; charset=ISO-8859-1\">")
  println("  <title>Nightly integration test</title>")
  println("  <meta content=\"Philipp Ruemmer\" name=\"author\">")
  println("</head>")
  println("<body>")

  println("<body>")

  println("<table align=\"center\" border=\"1\" cellpadding=\"3\" cellspacing=\"2\">")
  println("  <tbody>")
  println("    <tr>")
  println("      <th></th><th></th><th></th>")

  for (v <- allVersions)
    println("      <th><a href=\"" + v + ".log\">" + v + "</a></th>")

  println("    </tr>")

  val reader = new java.io.BufferedReader (new java.io.FileReader(benchFile))
    
  def printTime(m : Int) : String = "%.1fs".format(m.toFloat / 1000.0)

  var str = reader.readLine
  while (str != null) {
    println("    <tr>")

    println("      <td>" + str + "</td>")
    val props = new BenchProperties(new File(benchmarkDir + str))

    println("<td>")
    println(props.status.getOrElse("?"))
    println("</td>")
    println("<td>")
    println(props.rating.getOrElse("?"))
    println("</td>")

    for (v <- allVersions) {
      print("      ")

      print((logResults(v) get str) match {
        case Some(AnyTheoremResult(m)) =>
          "<td>&#10004; " + printTime(m)
        case Some(InconclusiveResult(m)) =>
          "<td bgcolor=\"Cyan\">&#10007; " + printTime(m)
        case Some(TimeoutResult(m)) =>
          "<td bgcolor=\"Red\">T/O"
        case Some(ErrorResult(m)) =>
          "<td bgcolor=\"Red\">Err " + printTime(m)
        case None =>
          "<td>"
      })

      println("</td>")
    }

    println("    </tr>")

    str = reader.readLine
  }
  
  println("  </tbody>")
  println("</table>")

  println("</body>")
  println("</html>")

}

////////////////////////////////////////////////////////////////////////////////

object BenchProperties {

    private val Status = """% +Status +: *([^ ]+) *$""".r
    private val Rating = """% +Rating +: *([0-9.]+) .*$""".r

}

class BenchProperties(benchmark : File) {

  import BenchProperties._

  val (status, rating) = {
    val reader = new java.io.BufferedReader (new java.io.FileReader(benchmark))

    var status : Option[String] = None
    var rating : Option[String] = None

    var str = reader.readLine
    while (str != null) {
      str match {
        case Status(s) => status = Some(s.trim)
        case Rating(s) => rating = Some(s.trim)
        case _ => // nothing
      }
      str = reader.readLine
    }

    reader.close

    (status, rating)
  }

}
