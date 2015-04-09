package ccu;

class CCUInstance[Term, Fun](
  id : Int, 
  solver : CCUSolver,
  problem : CCUSimProblem,
  termMap : Map[Term, Int]) {

  // var origTerms = List() : Seq[Term]
  // var origDomains = Map() : Map[Term, Set[Term]]
  // var origFunctions = List() : Seq[Seq[(Fun, Seq[Term], Term)]]
  // var origGoals = List() : Seq[Seq[Seq[(Term, Term)]]]

  var model = None : Option[Map[Term, Term]]


  def confirmActive = {
    if (solver.curId != id)
      throw new Exception("New instance has been created by solver")
  }

  def solve : Result.Result = {
    confirmActive
    val result = 
      try {
        solver.solveAsserted(problem)
      } catch {
        case to : org.sat4j.specs.TimeoutException => {
          ccu.Result.UNKNOWN
        }
      }

    println("result: " + result)
    result
  }

  def solveAsserted = {
    confirmActive
    solver.solveAsserted(problem)
  }

  def notUnifiable(prob : Int, s : Term, t : Term) : Boolean = {
    confirmActive
    // TODO: Does this work?
    (for (i <- termMap get s;
          j <- termMap get t)
     yield (!problem(prob).DQ(i, j))) getOrElse (s != t)

  }

  def unsatCore(timeout : Int) = {
    confirmActive
    val core =
      try {
        solver.unsatCore(problem, timeout)
      } catch {
        case to : org.sat4j.specs.TimeoutException => {
          (0 until problem.size)
        }
      }
    core
  }

  def print = println("SOMETHING SHOULD BE PRINTED")
     // solver.problem.print

}
