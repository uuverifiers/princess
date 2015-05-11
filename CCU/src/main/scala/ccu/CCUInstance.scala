package ccu;

import java.io.FileOutputStream
import java.io.ObjectOutputStream
import java.io.File


class CCUInstance[Term, Fun](
  id : Int, 
  solver : CCUSolver,
  val problem : CCUSimProblem,
  termMap : Map[Term, Int]) {

  var model = None : Option[Map[Term, Term]]


  def confirmActive = {
    if (solver.curId != id)
      throw new Exception("New instance has been created by solver")
  }

  def solve : Result.Result = {
    confirmActive

    val retval = 
      if (problem.solvable == false) {
        ccu.Result.UNSAT
      } else {
        try {
          solver.solve(problem, true)
        } catch {
          case to : org.sat4j.specs.TimeoutException => {
            ccu.Result.UNKNOWN
          }
        }
      }
    retval
  }

  def solveAsserted = {
    confirmActive
    solver.solve(problem, true)
  }

  def notUnifiable(prob : Int, s : Term, t : Term) : Boolean = {
    confirmActive
    // TODO: Does this work?
    (for (i <- termMap get s;
          j <- termMap get t)
     yield (!problem(prob).baseDQ(i, j))) getOrElse (s != t)

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

  // TODO: fix previous solution fix
  def checkPreviousSolution = {
    // var ss = true
    // if (model.isDefined) {
    //   val oldModel = model.get
    //   val newTerms = problem.terms
    //   val newModel =
    //     (for (t <- newTerms) yield {
    //       val newKey = t
    //       val oldAss = oldModel.getOrElse(t, t)
    //       val newAss = termMap.getOrElse(oldAss, newKey)
    //       (newKey, newAss)
    //     }).toMap



    //   // println("Checking previous model...")
    //   for (p <- problem.subProblems) {
    //     if (!solver.verifySolution(problem.terms, newModel, p.funEqs, p.goal)) {
    //       // println("\tNO")
    //       ss = false
    //     }
    //   }

    //   // Update model
    //   if (ss) {
    //     model = Some((for ((k, v) <- newModel) yield {
    //       (problem.intMap(k), problem.intMap(v))
    //     }).toMap)
    //   }

    // } else {
    //   ss = false
    // }

    // ss
  }

}
