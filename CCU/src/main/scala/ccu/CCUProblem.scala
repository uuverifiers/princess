package ccu;

// import argonaut._, Argonaut._
// import scalaz._, Scalaz._

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
  @transient val DQ : Disequalities,
  @transient val baseDQ : Disequalities) 
    extends Serializable {

  override def toString = {
    "CCUSubProblem"
  }

  def solvable = {
    // subgoalsat(0) = true of subgoal(0) is solvable
    val subgoalsat = for (subgoal <- goal.subGoals) yield
      (for ((s, t) <- subgoal) yield DQ(s, t)).foldRight(true)(_ && _)

    subgoalsat.foldRight(false)(_ || _)
  }

  def verifySolution(solution : Map[Int, Int]) = {
    val uf = Util.CCunionFind(terms, funEqs, solution.toList)
    var satisfiable = false

    for (subGoal <- goal.subGoals) {
      var subGoalSat = true

      var allPairsTrue = true
      for ((s,t) <- subGoal) {
        if (uf(s) != uf(t)) {
          allPairsTrue = false
        }

        if (!allPairsTrue)
          subGoalSat = false
      }
      if (subGoalSat) {
        satisfiable = true
      }
    }
    satisfiable    
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
      str += "| terms: " + subProblems(p).terms + "\n"
      str += "| domains: " + subProblems(p).domains + "\n"
      str += "| funEqs: " + subProblems(p).funEqs + "\n"
      str += "| goal: " + subProblems(p).goal + "\n"
      // str += "| DQ: " + subProblems(p).DQ + "\n"
      // str += "| baseDQ: " + subProblems(p).baseDQ + "\n"
      str += subProblems(p).toString + "\n"
    }
    str += "\\\\-------------\n"
    str
  }

  def apply(i : Int) = subProblems(i)

  def solvable = subProblems.map(_.solvable).foldRight(true)(_ && _)


  // implicit def CCUGoalEncodeJson: EncodeJson[CCUGoal] =
  //   EncodeJson((g : CCUGoal) =>
  //     ("subGoals" := g.subGoals.map(_.toList).toList) ->: jEmptyObject)

  // implicit def CCUEqEncodeJson: EncodeJson[CCUEq] =
  //   EncodeJson((eq : CCUEq) =>
  //     ("fun" := eq.eq._1) ->: ("args" := eq.eq._2.toList) ->:
  //       ("res" := eq.eq._3) ->: jEmptyObject)

  // implicit def CCUSubProblemEncodeJson: EncodeJson[CCUSubProblem] =
  //   EncodeJson((sp: CCUSubProblem) =>
  //     ("terms" := sp.terms.toList) ->: ("domains" := sp.domains.toList) ->:
  //       ("funEqs" := sp.funEqs.toList) ->: ("goal" := sp.goal) ->: jEmptyObject)

  // implicit def CCUSimProblemEncodeJson: EncodeJson[CCUSimProblem] =
  //   EncodeJson((p: CCUSimProblem) =>
  //     ("terms" := p.terms.toList) ->: ("domains" := p.domains.toList) ->:
  //       ("bits" := p.bits) ->: ("order" := p.order.toList) ->:
  //       ("subProblem" := p.subProblems.toList) ->: jEmptyObject)

  def JSON : String = {
    // this.asJson.toString
    "JSON DISABLED"
  }

  def verifySolution(solution : Map[Int, Int]) = {
    subProblems.forall(_.verifySolution(solution))
  }

}
