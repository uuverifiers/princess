package ccu;

class CCUGoal(val subGoals : Seq[Seq[(Int, Int)]]) {}

class CCUEq(val eq : (Int, Seq[Int], Int)) {}

class CCUSubProblem(
  val terms : Seq[Int],
  val domains : Map[Int, Set[Int]],
  val funEqs : Seq[CCUEq],
  val goal : CCUGoal,
  val DQ : Disequalities) {

  override def toString = {
    var str = ""
    str += funEqs.map(x => { val (f, a, r) = x.eq; f + ":" + a.mkString(":")  + ":" + r }).mkString(",") + "\n"
    str += goal.subGoals.map(x => x.map(y => y._1 + "." + y._2).mkString(":")).mkString(",")
    str
  }
}

class CCUSimProblem(
  val terms : Seq[Int],
  val domains : Map[Int, Set[Int]],
  val bits : Int,
  val baseDI : Seq[Array[Array[Int]]],
  val order : Seq[Int],
  val subProblems : Seq[CCUSubProblem]) {

  val size = subProblems.length
  var activeSubProblems = Array.fill[Boolean](size)(true)

  var result = None : Option[ccu.Result.Result]
  var intAss = Map() : Map[Int, Int]

  override def toString  = {
    var str = ""
    str += "//-------------\n"
    for (t <- terms)
      str += "| " + t + " = {" + (domains.getOrElse(t, Set(t))).mkString(", ") + "}" + "\n"
    str += "| Size: " + size + "\n"
    for (p <- 0 until size) {
      str += "+--------\n"
      str += "| funEqs: " + subProblems(p).funEqs + "\n"
      str += "| goal: " + subProblems(p).goal + "\n"
    }
    str += "\\\\-------------\n"
    str
  }

  def apply(i : Int) = subProblems(i)

  def deactivateProblem(p : Int) = {
    activeSubProblems(p) = false
  }

  def activateProblem(p : Int) = {
    activeSubProblems(p) = true
  }

  // TODO: SERIALIZE?
  def output = {
    import java.io._
    val writer = new PrintWriter(new File("test.txt"))
    var output = ""
    output += subProblems.length + "\n"
    output += domains.map(x => { val (k,v) = x; k + ":" + v.mkString(",") }).mkString(" ") + "\n"
    output += subProblems.mkString("\n")
    writer.write(output)
    writer.close()
  }
}
