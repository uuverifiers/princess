import java.io._

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

val timeout = 60000
val cmd = "../princess"
val input = " problems/*"
val tableOut = " &> logs/" + newLogNumber + ".table.log"
val lazyOut = " &> logs/" + newLogNumber + ".lazy.log"
val args = 
  " +triggersInConjecture +genTotalityAxioms -tightFunctionScopes" +
    " -clausifier=simple +reverseFunctionalityPropagation -boolFunsAsPreds" +
    " -triggerStrategy=allUni -resolutionMethod=nonUnifying" +
    " -timeout=" + timeout
println("echo Running Tablesolver...")
println(cmd + args + input + tableOut)
println("echo Running Lazysolver...")
println(cmd + args + input + lazyOut)
