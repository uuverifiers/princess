import java.io.File
import scala.collection.mutable.{HashMap => MHashMap}


object LogReader {
    private val Loading    = """Loading (.*) \.\.\.""".r
    private val SZS        = """% SZS status (.*) for .*""".r
    private val Time       = """([0-9]+)ms""".r
    private val Killed     = """Killed""".r
    private val UNKNOWN    = """UNKNOWN""".r
    private val OOM        = """Out of memory, giving up""".r
    private val Stack      = """Stack overflow, giving up""".r
    private val Explosion  = """Unexpected explosion during preprocessing""".r
    private val Clausifier = """Clausification timed out""".r
    private val CCU        = """CCUsolver timeout!""".r
    private val TimeoutMillis = 240000
}

class LogReader(logFile : File) {
  import LogReader._
  import Status._

  val results : Map[String, Status.StrategyResult] = {
         print("Reading " + logFile.getName + " ...")
         val reader = new java.io.BufferedReader (new java.io.FileReader(logFile))
    
         var str = reader.readLine
         var currentFile : String = ""
         var result : Int => StrategyResult = TheoremResult(_)
         val allResults = new MHashMap[String, StrategyResult]
      
         def checkError : Unit = {
           if (currentFile != "" && !(allResults contains currentFile))
             allResults += (currentFile -> TimeoutResult(TimeoutMillis))
           currentFile = ""
         }

         while (str != null) {
           str match {
             case Loading(name)                => {
               checkError
               currentFile = (name split "/").last
             }
             case SZS("Theorem" |
                      "Unsatisfiable")         => result = TheoremResult(_)
             case SZS("CounterSatisfiable" |
                      "Satisfiable" |
                      "GaveUp") |
                  UNKNOWN()                    => result = InconclusiveResult(_)
             case SZS("Timeout")               => result = TimeoutResult(_)
             case SZS("Error")                 => result = ErrorResult(_)
                                                  allResults += (currentFile -> result(0))
             case Time(millis)                 => allResults += (currentFile -> result(millis.toInt))
/*             case Killed() | OOM() | Stack() |
                  Explosion() | Clausifier() |
                  CCU()                        => allResults += (currentFile ->
                                                           TimeoutResult(TimeoutMillis)) */
             case _                            => // nothing
           }
           str = reader.readLine
         }
    
         checkError

         println(" " + allResults.size + " records")

         allResults.toMap
  }
}
