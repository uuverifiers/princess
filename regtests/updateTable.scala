import java.io._
import scala.collection.mutable.{Map, ListBuffer}

def getLogFiles = {
  val f = new File("logs/")
  val files = f.listFiles.filter(x => x.toString.endsWith(".log"))
  val logs = files.map(_.toString).map(_.split('/')(1))
  val numbers = logs.map(_.split('.')(0)).toSet.toList.sorted
  numbers.reverse
}

def parseFile(file : String) = {
  val map = Map() : Map[String, (String, String)]
  val lines = scala.io.Source.fromFile(file).getLines
  for (line <- lines; if line matches "REGRESSION:.*") {
    val split = line.split(':')
    val solver = split(1)
    val name = split(2)
    val result = split(3)
    val time = split(4)
    map += name -> ((result, time))
  }
  (file, map)
}

def makeInitRow(numbers : Seq[String]) = {
  val output = ListBuffer() : ListBuffer[String]
  output += "<tr>"
  output += "<td>Problem</td>"
  for (n <- numbers) {
    output += "<td><a href=logs/" + n + ".table.log>" + n + " (table)</a></td>"
    output += "<td><a href=logs/" + n + ".lazy.log>" + n + " (lazy)</a></td>"
  }
  output += "</tr>"

  output.mkString("\n")
}

def makeRow(problem : String, maps : Seq[Map[String, (String, String)]]) = {
  val output = ListBuffer() : ListBuffer[String]
  output += "<tr>"
  output += "<td>" + problem + "</td>"
  for (map <- maps) {
    val (result, time) = map getOrElse (problem, ("-", ""))
    val nresult = result match {
      case "OK" => "&#10004;"
      case "FAIL" => "&#10007;"
      case str => str
    }

    output += "<td>" + nresult + " " + time + "</td>"
  }

  output += "</tr>"

  output.mkString("\n")
}

val tableMaps = 
  (for (f <- getLogFiles) yield parseFile("logs/" + f + ".table.log"))

val lazyMaps = 
  (for (f <- getLogFiles) yield parseFile("logs/" + f + ".lazy.log"))

val comb = tableMaps zip lazyMaps

val maps = 
  (for ((tmap, lmap) <- comb) yield List(tmap, lmap)).flatten

val problems =
  for (file <- new File("problems/").listFiles) 
  yield (file.toString.split("/")(1)).split('.')(0)


println("<html>")
println("<table border=1 align=center cellpadding=3 cellspacing=2>")
println(makeInitRow(getLogFiles))
for (p <- problems.sorted) {
  println(makeRow(p, maps.map(_._2)))
}
println("</table>")
println("</html>")



