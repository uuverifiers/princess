package ccu;

import org.sat4j.tools.GateTranslator
import org.sat4j.minisat.SolverFactory
import org.sat4j.specs.ISolver
import org.sat4j.core.VecInt

import scala.collection.mutable.{Set => MSet}


class LazySolver[Term, Fun](timeoutChecker : () => Unit, 
                              maxSolverRuntime : Long)  
    extends CCUSolver[Term, Fun](timeoutChecker, maxSolverRuntime) {

  def trySolution(problemOrder : List[Int],
    problem : CCUSimProblem,
    solution : Map[Int, Int]) : Option[Int] = 
  Timer.measure("LazySolver.trySolution") {

    // Check each problem one by one, adding blocking clauses
    // if any of the are UNSAT by this model
    var p = 0

    // Check if this is a solution


    // TODO: How to make loop better? I.e. remove return...
    while (p < problem.size) {
      val cp = problem(problemOrder(p))
      if (!cp.verifySolution(solution)) {
        return Some(problemOrder(p))
      }
      p += 1
    }

    None
  }

  def handleBlockingProblem(cp : CCUSubProblem, solution : Map[Int, Int],
  teqt : Array[Array[Int]], assignments : Map[Int, Seq[Int]]) = 
  Timer.measure("handleBlockingProblem") {
    // val DQ = new Disequalities(cp.baseDQ)
    val DQ = new Disequalities(cp.terms.max+1, cp.funEqs.toArray, timeoutChecker)

    // Could we replace this by just doing cascade-remove on the assignments?
    val uf = Util.CCunionFind(cp.terms, List(), solution.toList)

    for (s <- cp.terms; t <- cp.terms;
      if (s <= t); if (uf(s) == uf(t))) {
      DQ.cascadeRemove(s, t)
    }

    def heuristic(dq : (Int, Int)) = {
      val (s, t) = dq
      cp.domains(s).size
    }

    // Now we minimize DI to only contain "relevant" inequalities
    DQ.minimise(cp.terms, cp.goal.subGoals, cp.baseDQ, heuristic)

    // Remove all "base" inequalities, since they will always be there

    val ineqs = DQ.inequalities(cp.terms)

    val finalDQ = for ((s,t) <- ineqs; if cp.baseDQ(s, t)) yield (s, t)

    // println("Blocking clause size: " + finalDQ.length)

    val blockingClause =
      (for ((s,t) <- finalDQ) yield {
        if (teqt(s min t)(s max t) == -1)
          teqt(s min t)(s max t) =
            termEqTermAux(assignments(s), assignments(t))
        teqt(s min t)(s max t)
      }).toArray

    try {
      solver.addClause(new VecInt(blockingClause))
      bcCount += 1
      false
    } catch {
      case e : org.sat4j.specs.ContradictionException => {
        println("contradict")
        true
      }
    }
  }

  override def solveaux(problem : CCUSimProblem) 
      : (ccu.Result.Result, Option[Map[Int, Int]]) = 
  Timer.measure("LazySolver.solveaux") {
    reset
    bcCount = 0


    // Shows what bits are used to represent value of terms
    val assignments = createAssignments(problem)

    // Used to store what bits are equivalent to term equal term
    val teqt = Array.fill[Int](problem.terms.length, problem.terms.length)(-1)

    // Keeps track whether a subproblem has triggered UNSAT
    val blockingProblem = Array.ofDim[Boolean](problem.size)

    // If all problems are SAT or one problem is infeasible, we are done
    var allSat = false
    var infeasible = false

    var intAss = Map() : Map[Int, Int]

    // Check the "hardest" problem first!
    var problemOrder = List.tabulate(problem.size)(x => x)

    while (!infeasible && !allSat && solver.isSatisfiable()) {
      timeoutChecker()
      Timer.measure("LazySolver.assignmentsToSolution)") {
        intAss = assignmentsToSolution(assignments)
      }

      trySolution(problemOrder, problem, intAss) match {
        case Some(p) => {
          blockingProblem(problemOrder(p)) = true
          if (handleBlockingProblem(problem(problemOrder(p)), intAss,
            teqt, assignments))
            infeasible = true
          problemOrder = p::problemOrder.filter(_ != p)
        }

        case None => allSat = true
      }
    }
    if (allSat) {
      S.addEntry("LAZY>RESULT:SAT,BLOCKINGCLAUSES:" + bcCount)
      (ccu.Result.SAT, Some(intAss))
    } else {
      lastUnsatCore =
        (for (i <- 0 until problem.size; if (blockingProblem(i))) yield i)
      S.addEntry("LAZY>RESULT:UNSAT,BLOCKINGCLAUSES:" + bcCount)
      (ccu.Result.UNSAT, None)
    }
  }

  override def getStat(result : ccu.Result.Result) = {
    "LAZY>RESULT:" + result + ",BLOCKINGCLAUSES:" + bcCount
  }

  def unsatCoreAux(problem : CCUSimProblem, timeout : Int) = lastUnsatCore

  // println("Creating LazySolver...")

  // We automatically calculate unsatCore
  var lastUnsatCore = List() : Seq[Int]

  var bcCount = 0
}
