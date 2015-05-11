package ccu;

@SerialVersionUID(15L)
case class CCUGoal(val subGoals : Seq[Seq[(Int, Int)]]) extends Serializable {
  override def toString = {
    subGoals.mkString(" OR ")
  }
}

@SerialVersionUID(15L)
case class CCUEq(val eq : (Int, Seq[Int], Int)) extends Serializable {
  val fun = eq._1
  val args = eq._2
  val res = eq._3

  override def toString = {
    eq.toString
  }
}

@SerialVersionUID(15L)
case class CCUSubProblem(
  val terms : Seq[Int],
  val domains : Map[Int, Set[Int]],
  val funEqs : Seq[CCUEq],
  val goal : CCUGoal,
  // @transient var DQ : Disequalities,
  @transient val baseDQ : Disequalities) 
    extends Serializable {

  override def toString = {
    var str = ""
     // str += baseDI.map(x => x.mkString(" - ")).mkString("\n")
    str
  }

  def solvable = {
    // subgoalsat(0) = true of subgoal(0) is solvable
    val subgoalsat = for (subgoal <- goal.subGoals) yield
      (for ((s, t) <- subgoal) yield baseDQ(s, t)).foldRight(true)(_ && _)

    subgoalsat.foldRight(false)(_ || _)
  }
}

@SerialVersionUID(15L)
case class CCUSimProblem(
  val terms : Seq[Int],
  val domains : Map[Int, Set[Int]],
  val bits : Int,
  val order : Seq[Int],
  val subProblems : Seq[CCUSubProblem]) 
    extends Serializable {

  val size = subProblems.length

  override def toString  = {
    var str = ""
    str += "//-------------\n"
    for (t <- terms)
      str += "| " + t + " = {" + (domains.getOrElse(t, Set(t))).mkString(", ") + "}" + "\n"
    str += "| Size: " + size + "\n"
    str += "| Bits: " + bits + "\n"
    str += "| Order: " + order + "\n"
    for (p <- 0 until size) {
      str += "+--------\n"
      str += "| funEqs: " + subProblems(p).funEqs + "\n"
      str += "| goal: " + subProblems(p).goal + "\n"
      str += subProblems(p).toString + "\n"
    }
    str += "\\\\-------------\n"
    str
  }

  def apply(i : Int) = subProblems(i)

  def solvable = subProblems.map(_.solvable).foldRight(true)(_ && _)
}
