import scala.sys.process._
import java.io._
import scala.collection.mutable.ListBuffer
import scala.collection.mutable.Map
import scala.concurrent.Lock

//
//   UTIL
//

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

//
// OPEN FILES
//

val files =
  for (file <- new File("problems/").listFiles) yield file.toString
val cmd = "../princess  +triggersInConjecture +genTotalityAxioms -tightFunctionScopes -clausifier=simple +reverseFunctionalityPropagation -boolFunsAsPreds -triggerStrategy=allUni -resolutionMethod=nonUnifying -timeout=30000 " + files.mkString(" ")
println("cmd: " + cmd)
val lazycmd = cmd + " -CCU=lazy"
val tablecmd = cmd + " -CCU=table"
val newlog = newLogNumber
val lazyWriter = 
  new java.io.PrintWriter(new File("logs/" + newlog + ".lazy.log"))
val tableWriter = 
  new java.io.PrintWriter(new File("logs/" + newlog + ".table.log"))


// writeOut
def wo(w : PrintWriter, str : String) = {
  w.println(str)
  w.flush()
}

// 
// RUN TESTS
//


println("Running TableSolver...")
tablecmd ! ProcessLogger(
  (o : String) => wo(tableWriter, o),
  (e : String) => wo(tableWriter, e)
)
println("\tDone!")

println("Running LazySolver...")
lazycmd ! ProcessLogger(
  (o : String) => wo(lazyWriter, o),
  (e : String) => wo(lazyWriter, e))
println("\tDone!")

// println("COMPLETE\n")
// val lazyResults = Map() : Map[String, String]
// val lazyTimes = Map() : Map[String, Int]
// val tableResults = Map() : Map[String, String]
// val tableTimes = Map() : Map[String, Int]
// var curFile = ""

// def handleOutput(str : String, 
//   resMap : Map[String, String], 
//   timeMap : Map[String, Int],
//   writer : PrintWriter) = {
//   println(str)
//   writer.println(str)
//   writer.flush()
//   if ((str contains "Error") || (str contains "ERROR") || (str contains "GaveUp")) {
//     resMap += (curFile -> "ERROR")
//     timeMap += (curFile -> 0)
//     done += 1
//     println("ERROR -> DONE = " + done)
//     if (done == 2)
//       lock.release()
//   } else if (str contains "SZS") {
//     val split = str.split(" ")
//     val status = split(3)
//     val name = (split(5).split('.'))(0)
//     resMap += name -> status
//   } else if (str matches "[0-9]*ms") {
//     timeMap += curFile -> str.substring(0, str.length - 2).toInt
//     done += 1
//     if (done == 2)
//       lock.release()
//   }
// }

// val lazyLogger = ProcessLogger(
//     (o: String) => handleOutput(o, lazyResults, lazyTimes, lazyWriter),
//     (e : String) => handleOutput(e, lazyResults, lazyTimes, lazyWriter))

// val tableLogger = ProcessLogger(
//     (o: String) => handleOutput(o, tableResults, tableTimes, tableWriter),
//     (e: String) => handleOutput(e, tableResults, tableTimes, tableWriter))


// //
// // UPDATE ANSWERS
// //

// def updateAnswer(problem : String, answer : String) = {
//   println("UPDATING ANSWER!")
//   val fout = "regtests.out"
//   val fw = new FileWriter(fout, true)
//   fw.write(problem + "\t" + answer + "\n")
//   fw.close()
// }


// //
// // VERIFY ANSWER
// //

// val newResults = Map() : Map[String, String]

// var lazyFail = 0
// var lazyTOs = 0
// var lazyErrors = 0
// var tableFail = 0
// var tableTOs = 0
// var tableErrors = 0

// val diffs = ListBuffer() : ListBuffer[String]

// def verify(problem : String) = {
//   println(problem)
//   val old = realResults.contains(problem)

//   // Timeouts
//   val lazyTO = lazyResults(problem) == "Timeout"
//   val tableTO = tableResults(problem) == "Timeout"
//   val lazyError = lazyResults(problem) == "ERROR"
//   val tableError = tableResults(problem) == "ERROR"

//   if (lazyTO) {
//     lazyTOs += 1
//     println("\tLAZY:\tT/O")
//     lazyWriter.println("REGRESSION:LAZY:" + problem + ":UNKNOWN:T/O")
//   } else if (lazyError) {
//     lazyErrors += 1
//     println("\tLAZY:\tERROR")
//     lazyWriter.println("REGRESSION:LAZY:" + problem + ":ERROR:ERROR")
//   } else if (old) {
//     val lt = "(" + lazyTimes(problem) + " ms)"
//     if (lazyResults(problem) == realResults(problem)) {
//       println("\tLAZY:\tOK!" + lt)
//     lazyWriter.println("REGRESSION:LAZY:" + problem + ":OK:" + lt)
//     } else {
//       lazyFail += 1
//     lazyWriter.println("REGRESSION:LAZY:" + problem + ":FAIL:" + lt)
//       println("\tLAZY:\tFAIL" + lt)
//     }
//   }

//   if (tableTO) {
//     tableTOs += 1
//     println("\tTABLE:\tT/O")
//     tableWriter.println("REGRESSION:TABLE:" + problem + ":UNKNOWN:T/O")
//   } else if (tableError) {
//     tableErrors += 1
//     println("\tTABLE:\tERROR")
//     tableWriter.println("REGRESSION:TABLE:" + problem + ":ERROR:ERROR")
//   } else if (old) {
//     val tt = "(" + tableTimes(problem) + " ms)"
//     if (tableResults(problem) == realResults(problem)) {
//       tableWriter.println("REGRESSION:TABLE:" + problem + ":OK:" + tt)
//       println("\tTABLE:\tOK!" + tt)
//     } else {
//       tableFail += 1
//       tableWriter.println("REGRESSION:TABLE:" + problem + ":FAIL:" + tt)
//       println("\tTABLE:\tFAIL" + tt)
//     }
//   }

//   if (!lazyTO && !tableTO && 
//     !lazyError && !tableError &&
//     lazyResults(problem) != tableResults(problem)) {
//     println("------->DIFF")
//     diffs += problem
//   }

//   if (!old) {
//     println("\tNEW!")
//     if (!lazyTO)
//       updateAnswer(problem, lazyResults(problem))
//     else if (!tableTO)
//       updateAnswer(problem, tableResults(problem))
//   }

//   lazyWriter.flush()
//   tableWriter.flush()
// }





// //
// // UPDATE ANSWERS
// //

// def printToFile(f : java.io.File)(op : java.io.PrintWriter => Unit) {
//   val p = new java.io.PrintWriter(f)
//   try { op(p) } finally { p.close() }
// }

// if (!newResults.isEmpty) {
//   val output = ListBuffer() : ListBuffer[String]
//   for ((prob, ans) <- realResults)
//     output += prob + "\t" + ans

//   for ((prob, ans) <- newResults)
//     output += prob + "\t" + ans

//   val fout = "regtests.out"
//   println("Writing new answers to: " + fout)
//   printToFile(new File(fout)) {
//     p => output.foreach(p.println)
//   }
// }

// println("//--------------")
// println("Lazy fail:\t" + lazyFail)
// println("Lazy T/O:\t" + lazyTOs)
// println("Table fail:\t" + tableFail)
// println("Table T/O:\t" + tableTOs)
// for (prob <- diffs) 
//   println("DIFF:\t" + prob)

// lazyWriter.close()
// tableWriter.close()
