import scala.sys.process._
import java.io._
import scala.collection.mutable.ListBuffer
import scala.collection.mutable.Map
import scala.concurrent.Lock


//
//  UTIL
//
var done = 0
val lock = new Lock()

//
//  READ ANSWERS
//
val answers = scala.io.Source.fromFile("regtests.out").getLines
val realResults = Map() : Map[String, String]

for (line <- answers) {
  val split = line.split("\t")
  realResults += split(0) -> split(1)
}


//
// OPEN FILES
//

val files =
  for (file <- new File("problems/").listFiles) yield file.toString
val cmd = "../princess -timeout=60000"

def newLogNumber = {
  val f = new File("logs/")
  val files = f.listFiles.filter(x => x.toString.endsWith(".log"))
  if (!files.isEmpty) {
    val logs = files.map(_.toString).map(_.split('/')(1))
    val ints = logs.map(_.split('.')(0)).map(_.toInt)
    ints.sorted.max + 1
  } else {
    1
  }
}

val newlog = newLogNumber
val lazyWriter = 
  new java.io.PrintWriter(new File("logs/" + newlog + ".lazy.log"))
val tableWriter = 
  new java.io.PrintWriter(new File("logs/" + newlog + ".table.log"))

// 
// RUN TESTS
//
val lazyResults = Map() : Map[String, String]
val lazyTimes = Map() : Map[String, Int]
val tableResults = Map() : Map[String, String]
val tableTimes = Map() : Map[String, Int]
var curFile = ""

def handleOutput(str : String, 
  resMap : Map[String, String], 
  timeMap : Map[String, Int],
  writer : PrintWriter) = {
  writer.println(str)
  writer.flush()
  if (str contains "SZS") {
    val split = str.split(" ")
    val status = split(3)
    val name = (split(5).split('.'))(0)
    curFile = name
    resMap += name -> status
  } else if (str matches "[0-9]*ms") {
    timeMap += curFile -> str.substring(0, str.length - 2).toInt
    done += 1
    if (done == 2)
      lock.release()
  }
}

val lazyLogger = ProcessLogger(
    (o: String) => handleOutput(o, lazyResults, lazyTimes, lazyWriter),
    (e : String) => handleOutput(e, lazyResults, lazyTimes, lazyWriter))

val tableLogger = ProcessLogger(
    (o: String) => handleOutput(o, tableResults, tableTimes, tableWriter),
    (e: String) => handleOutput(e, tableResults, tableTimes, tableWriter))


//
// UPDATE ANSWERS
//

def updateAnswer(problem : String, answer : String) = {
  println("UPDATING ANSWER!")
  val fout = "regtests.out"
  val fw = new FileWriter(fout, true)
  fw.write(problem + "\t" + answer + "\n")
  fw.close()
}


//
// VERIFY ANSWER
//

val newResults = Map() : Map[String, String]

var lazyFail = 0
var lazyTOs = 0
var tableFail = 0
var tableTOs = 0

val diffs = ListBuffer() : ListBuffer[String]

def verify(problem : String) = {
  println(problem)
  val old = realResults.contains(problem)

  // Timeouts
  val lazyTO = lazyResults(problem) == "Timeout"
  val tableTO = tableResults(problem) == "Timeout"

  if (lazyTO) {
    lazyTOs += 1
    println("\tLAZY:\tT/O")
    lazyWriter.println("REGRESSION:LAZY:" + problem + ":UNKNOWN:T/O")
    
  } else if (old) {
    val lt = "(" + lazyTimes(problem) + " ms)"
    if (lazyResults(problem) == realResults(problem)) {
      println("\tLAZY:\tOK!" + lt)
    lazyWriter.println("REGRESSION:LAZY:" + problem + ":OK:" + lt)
    } else {
      lazyFail += 1
    lazyWriter.println("REGRESSION:LAZY:" + problem + ":FAIL:" + lt)
      println("\tLAZY:\tFAIL" + lt)
    }
  }

  if (tableTO) {
    tableTOs += 1
    println("\tTABLE:\tT/O")
    tableWriter.println("REGRESSION:TABLE:" + problem + ":UNKNOWN:T/O")
  } else if (old) {
    val tt = "(" + tableTimes(problem) + " ms)"
    if (tableResults(problem) == realResults(problem)) {
      tableWriter.println("REGRESSION:TABLE:" + problem + ":OK:" + tt)
      println("\tTABLE:\tOK!" + tt)
    } else {
      tableFail += 1
      tableWriter.println("REGRESSION:TABLE:" + problem + ":FAIL:" + tt)
      println("\tTABLE:\tFAIL" + tt)
    }
  }

  if (!lazyTO && !tableTO && lazyResults(problem) != tableResults(problem)) {
    println("------->DIFF")
    diffs += problem
  }

  if (!old) {
    println("\tNEW!")
    if (!lazyTO)
      updateAnswer(problem, lazyResults(problem))
    else if (!tableTO)
      updateAnswer(problem, tableResults(problem))
  }

  lazyWriter.flush()
  tableWriter.flush()
}


  lock.acquire()
// File-by-file
for (f <- files) {
  curFile = f
  val tableCmd = cmd + " -CCU=table " + f
  tableCmd ! tableLogger

  val lazyCmd = cmd + " -CCU=lazy " + f
  lazyCmd ! lazyLogger

  val name = (f.split("/")(1)).split('.')(0)

  lock.acquire()
  verify(name)
  done = 0

}

println("COMPLETE\n")


//
// UPDATE ANSWERS
//

def printToFile(f : java.io.File)(op : java.io.PrintWriter => Unit) {
  val p = new java.io.PrintWriter(f)
  try { op(p) } finally { p.close() }
}

if (!newResults.isEmpty) {
  val output = ListBuffer() : ListBuffer[String]
  for ((prob, ans) <- realResults)
    output += prob + "\t" + ans

  for ((prob, ans) <- newResults)
    output += prob + "\t" + ans

  val fout = "regtests.out"
  println("Writing new answers to: " + fout)
  printToFile(new File(fout)) {
    p => output.foreach(p.println)
  }
}

println("//--------------")
println("Lazy fail:\t" + lazyFail)
println("Lazy T/O:\t" + lazyTOs)
println("Table fail:\t" + tableFail)
println("Table T/O:\t" + tableTOs)
for (prob <- diffs) 
  println("DIFF:\t" + prob)

lazyWriter.close()
tableWriter.close()