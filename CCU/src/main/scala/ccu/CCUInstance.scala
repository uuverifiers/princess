package ccu;

import java.io.FileOutputStream
import java.io.ObjectOutputStream
import java.io.File

import scala.collection.mutable.{Map => MMap}


class CCUInstance[Term, Fun](
  id : Int, 
  solver : CCUSolver[Term, Fun],
  val problem : CCUSimProblem,
  val termMap : Map[Term, Int],
  originalDomains : Map[Term, Set[Term]]) {

  var model = None : Option[Map[Int, Int]]

  def confirmActive = {
    if (solver.curId != id)
      throw new Exception("New instance has been created by the solver")
  }

  def solve : Result.Result = {
    confirmActive

    val (solved, newModel) =
      if (solver.previousInstance.isDefined)
        checkPreviousSolution(solver.previousInstance.get)
      else
        (false, None)

    if (solved) {
      model = newModel

      assert(problem.verifySolution(model.get))

      solver.previousInstance = Some(this)
      (ccu.Result.SAT)
    } else {
      // --- TRIVIAL SOLUTION CHECK ---
      val ts = trivialSolution(problem.domains, problem.subProblems.map(_.goal.subGoals))
      if (ts.isDefined) {
        // Make model
        // println("TRIVIAL SOLUTION FOUND")
        model = Some(ts.get.toMap)
        return ccu.Result.SAT
        solver.previousInstance = Some(this)
      }

      val retval =
        try {
          solver.solve(problem, true)
        } catch {
          case to : org.sat4j.specs.TimeoutException => {
            (ccu.Result.UNKNOWN, None)
          }
        }

      model = retval._2
      solver.previousInstance = Some(this)
      retval._1
    }
  }

  def notUnifiable(prob : Int, s : Term, t : Term) : Boolean = {
    confirmActive
    // TODO: Does this work?
    (for (i <- termMap get s;
          j <- termMap get t)
     yield (!problem(prob).baseDQ(i, j))) getOrElse (s != t)

  }

  def getModel = {
    if (!model.isDefined)
      throw new Exception("Trying to get undefined model")

    val b = termMap.map(_.swap)

    val res =
      (for ((k, v) <- model.get) yield {
        (b(k), b(v))
      }).toMap

    assert(originalDomains forall {
             case (x, dom) => dom contains res.getOrElse(x, x)
           })

    res
  }

  def unsatCore(timeout : Int) = {
    // println("unsatCore...")
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

  def checkPreviousSolution(prevInst : CCUInstance[Term, Fun]) :
      (Boolean, Option[Map[Int, Int]]) = {
    if (prevInst.model.isDefined) {
      var ss = true 
      val intMap = termMap map {_.swap} : Map[Int, Term]
      val oldModel = prevInst.model.get : Map[Int, Int]
      val oldTermMap = prevInst.termMap : Map[Term, Int]
      val oldIntMap = oldTermMap map {_.swap} : Map[Int, Term]

      val newModel =
        (for (t <- problem.terms) yield {
          // Did this term exists in previous step
          val newAss =
            if (oldTermMap contains intMap(t)) {
              // Translate it to old int rep
              val oldInt = oldTermMap(intMap(t))

              // Check if it was assigned?
              val oldAss = oldModel getOrElse (oldInt, oldInt)

              // Check if the old assignment still exists, else identity
              termMap.getOrElse(oldIntMap(oldAss), t)
            } else {
              t 
            }

          (t, newAss)
        }).toMap

      // Check if newModel is valid
      val valid = 
        (newModel forall {
          case (t, v) => problem.domains(t) contains v
        })

      if (valid && problem.verifySolution(newModel)) (true, Some(newModel))
      else (false, None)
    }
    else (false, None)
  }


//
// TRIVIAL SOLUTIONS
//

  def tsPairs(assignments : MMap[Int, Int], domains : Map[Int, Set[Int]],
    goals : Seq[(Int, Int)]) : (Option[MMap[Int, Int]]) = {

    if (goals.isEmpty) {
      Some(assignments)
    } else {
      // Pick out first goal and make larger term LHS
      val (s, t) = goals.head
      val lhs = s max t
      val rhs = s min t

      if (assignments.contains(lhs)) {
        if (assignments(lhs) == rhs)
          tsPairs(assignments, domains, goals.tail)
        else
          None
      } else {
        val lhsDomain = domains.getOrElse(lhs, Set())
        if (lhsDomain contains rhs) {
          assignments(lhs) = rhs
          tsPairs(assignments, domains, goals.tail)
        } else {
          None
        }
      }
    }
  }

  // Returns an (extended) assignment if one is possible, else None
  def tsSubgoals(
    domains : Map[Int, Set[Int]],
    subGoals : Seq[Seq[(Int, Int)]],
    assignment : Map[Int, Int]) : Option[MMap[Int, Int]] = {
    for (pairs <- subGoals) {
      val ass = MMap() : MMap[Int, Int]
      for ((k, v) <- assignment)
        ass(k) = v
      tsPairs(ass, domains, pairs) match {
        case Some(ass) => Some(ass)
        case None =>
      }
    }
    None
  }

  def trivialSolution(domains : Map[Int, Set[Int]],
    goals : Seq[Seq[Seq[(Int, Int)]]]) : (Option[MMap[Int, Int]]) = {
    var assignment = MMap() : MMap[Int, Int]

    // All problems must be satisfied
    for (subGoals <- goals) {
      tsSubgoals(domains, subGoals, assignment.toMap) match {
        case Some(ass) => assignment = ass
        case None => return None
      }
    }

    Some(assignment)
  }
}
