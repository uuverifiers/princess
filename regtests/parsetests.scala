import scala.sys.process._
import java.io._
import scala.collection.mutable.ListBuffer
import scala.collection.mutable.Map

//
//   UTIL
//
def logFiles = {
  val f = new File("logs/")
  val files = f.listFiles.map(_.toString).filter(x => x.endsWith(".log"))
  val lazyFiles = files.filter(_.contains("lazy"))
  val tableFiles = files.filter(_.contains("table"))
  (tableFiles.sortBy(x => x.split("/")(1).split('.')(0).toInt).reverse, 
    lazyFiles.sortBy(x => x.split("/")(1).split('.')(0).toInt).reverse)
}

//
//  READ ANSWERS
//
val answerFile = scala.io.Source.fromFile("regtests.out").getLines
val answers = Map() : Map[String, String]

for (line <- answerFile) {
  val split = line.split("\t")
  answers += split(0) -> split(1)
}

def isCorrect(problem : String, answer : String) = {
  if (answers contains problem) {
    answers(problem) == answer
  } else {
    answers += problem -> answer
    if (answer != "Timeout" && answer != "TIMEOUT") {
      println("UPDATING ANSWER!")
      val fout = "regtests.out"
      val fw = new FileWriter(fout, true)
      fw.write(problem + "\t" + answer + "\n")
      fw.close()
    }
    true
  }
}

//
//   PARSE LOG
//

val (tableLogs, lazyLogs) = logFiles
println("Parsing: ")
println("\tTable: " + tableLogs.mkString(", "))
println("\tLazy: " + lazyLogs.mkString(", "))


val lazyResults = Map() : Map[String, String]
val lazyTimes = Map() : Map[String, Int]
val tableResults = Map() : Map[String, String]
val tableTimes = Map() : Map[String, Int]

def handleFile(filename : String) = {

  val lines = scala.io.Source.fromFile(filename).getLines
  var curFile = ""
  var curResult = ""
  var curTime = ""

  val results = Map() : Map[String, (String, String, Boolean)]

  var done = false
  for (str <- lines) {
    if (curFile == "") {
      if (str contains "Loading") {
        curFile = str.split('/')(1).split('.')(0)
      }
    } else if ((str contains "Error") || 
      (str contains "ERROR") || 
      (str contains "GaveUp")) {
      curResult = "ERROR"
      curTime = "n/a"
      done = true
    } else if (str contains "SZS") {
      val split = str.split(" ")
      curResult = split(3)
    } else if (str matches "[0-9]*ms") {
      curTime = str.substring(0, str.length - 2)
      done = true
    }

    if (done) {
      val correct = isCorrect(curFile, curResult)
      results += curFile -> ((curResult, curTime, correct))
      done = false
      curFile = ""
    }
  }

  val name = filename.split('/')(1)
  (name, results)
}


val lazyMaps = lazyLogs.map(handleFile(_))
val tableMaps = tableLogs.map(handleFile(_))

//
//   UPDATE TABLE
//

def makeInitRow(numbers : Seq[String]) = {
  val output = ListBuffer() : ListBuffer[String]
  output += "<tr>"
  output += "<td>Problem</td>"
  for (n <- numbers) {
    output += "<td><a href=logs/" + n + ">" + n + "</a></td>"
  }
  output += "</tr>"

  output.mkString("\n")
}

def makeRow(problem : String, maps : Seq[Map[String, (String, String, Boolean)]]) = {
  val output = ListBuffer() : ListBuffer[String]
  output += "<tr>"
  output += "<td>" + problem + "</td>"
  for (map <- maps) {
    val (result, time, pass) = map getOrElse (problem, ("", "", true))
    val p = if (pass)
      "&#10004;"
    else
      "&#10007;"
    output += "<td>" + p + " " + time + "</td>"
  }

  output += "</tr>"

  output.mkString("\n")
}

val comb = tableMaps zip lazyMaps

val maps = 
  (for ((tmap, lmap) <- comb) yield List(tmap, lmap)).flatten


val problems =
  for (file <- new File("problems/").listFiles) 
  yield (file.toString.split("/")(1)).split('.')(0)


println("<html>")
val format = new java.text.SimpleDateFormat("dd/MM-hh:mm")
println(format.format(new java.util.Date()))
println("<table border=1 align=center cellpadding=3 cellspacing=2>")
val files = (for ((f, _) <- maps) yield f)
println(makeInitRow(files))
for (p <- problems.sorted) {
  println(makeRow(p, maps.map(_._2)))
}
println("</table>")
println("</html>")



