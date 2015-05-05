package ccu;

import org.sat4j.tools.GateTranslator
import org.sat4j.minisat.SolverFactory
import org.sat4j.specs.ISolver
import org.sat4j.core.VecInt

import scala.collection.mutable.{Set => MSet}


class LazySolver(timeoutChecker : () => Unit, 
                              maxSolverRuntime : Long)  
    extends CCUSolver(timeoutChecker, maxSolverRuntime) {

  // We automatically calculate unsatCore
  var lastUnsatCore = List() : Seq[Int]

  // minimises DI s.t. what remains is a set of inequalities
  // s.t. if any one of them is removed, the goals can be
  // fulfilled using functions.
  
  // This is inexact! For example, given a != b, b != c, c != d, we get
  // that a ~= c, b ~= d, d ~= a (where ~= is "could be equal"), this
  // by transitivity (in some cases) yields that a = b = c = d

  var bcCount = 0

  override def solveaux(problem : CCUSimProblem) 
      : (ccu.Result.Result, Option[Map[Int, Int]]) = {
    // Initialize problem and some useful values
    val terms = problem.terms
    val domains = problem.domains
    val bits = util.binlog(terms.length)

    // Reset and add default stuff
    this.reset

    // STATISTICS
    bcCount = 0

    // Shows what bits are used to represent value of terms
    val assignments = createAssignments(problem)

    // As long as the model is SAT, we can search for more solutions
    // Added for timing reasons
    def KeepOnGoing() = {
      // Timer.measure("SOLVE.SAT4J") {
      solver.isSatisfiable()
      // }
    }

    // Used to store what bits are equivalent to term equal term
    val teqt =
      Array.ofDim[Int](problem.terms.length, problem.terms.length)
    for (i <- 0 until problem.terms.length;
      j <- 0 until problem.terms.length)
      teqt(i)(j) = -1

    // Keeps track whether a subproblem has triggered UNSAT
    val blockingProblem = Array.ofDim[Boolean](problem.size)

    // If all problems are SAT, then we are done
    var allSat = false
    // If some problem is infeasible, we are done
    var infeasible = false
    var intAss = Map() : Map[Int, Int]

    // Check the "hardest" problem first!
    var problemOrder = List.tabulate(problem.size)(x => x)
    def prioritize(p : Int) = {
      problemOrder = p :: problemOrder.filter(_ != p)
    }

    while (!infeasible && !allSat && KeepOnGoing()) {
      timeoutChecker()

      intAss = assignmentsToSolution(assignments)

      allSat = true

      // Check each problem one by one, adding blocking clauses
      // if any of the are UNSAT by this model
      var p = 0

      while (allSat && p < problem.size) {
        // Check if this is a solutio
        val cp = problem(problemOrder(p))

        if (!verifySolution(terms, intAss, cp.funEqs, cp.goal)) {
          allSat = false
          blockingProblem(problemOrder(p)) = true

          // If not, we have to find a new model, but we should add a blocking
          // clause to not get the same model again

          // Find out DI (i.e. expand diseq by using FP calculation)
          // this gives a lower bound on inequalities (i.e. inequalities)
          // that MUST hold

          // TODO: Use problem.dq?
          val DQ = new Disequalities(problem.terms.length, cp.funEqs.toArray, timeoutChecker)

          val uf = util.CCunionFind(problem.terms,
            cp.funEqs, intAss.toList)

          for (s <- problem.terms; t <- problem.terms;
            if (s <= t); if (uf(s) == uf(t)))
            DQ.cascadeRemoveDQ(s, t)

          // Now we minimize DI to only contain "relevant" inequalities
          DQ.minimise(cp.goal.subGoals, cp.baseDI)
          val minDI = DQ.getINEQ()
          val noBaseDQ = for ((s,t) <- DQ.getINEQ(); if cp.baseDI(s)(t) != 0) yield (s, t)

          // The blocking clause states that one of the inequalities
          // in minDI must be false (i.e. equality must hold)

          // Remove all "base" inequalities, since they will always be there
          // no need trying to satisfy those
          // println("blockingClause: " + noBaseDQ.mkString(", "))
          val blockingClause =
            (for ((s,t) <- noBaseDQ) yield {
              if (teqt(s min t)(s max t) == -1) {
                val newT =
                  termEqTermAux(
                    assignments(s),
                    assignments(t))
                teqt(s min t)(s max t) = newT
              }
              teqt(s min t)(s max t)
            }).toArray

          try {
            // println("Adding blockingClause: " + blockingClause.mkString(" "))
            solver.addClause(new VecInt(blockingClause))
            bcCount += 1
          } catch {
            case e : org.sat4j.specs.ContradictionException => {
              infeasible = true
            }
          }

          prioritize(problemOrder(p))

        }
        p += 1
      }
    }

    if (allSat) {
      // SAT
      S.addEntry("LAZY>RESULT:SAT,BLOCKINGCLAUSES:" + bcCount)
      (ccu.Result.SAT, Some(intAss))
    } else {
      // UNSAT
      lastUnsatCore =
        (for (i <- 0 until problem.size; if (blockingProblem(i)))
        yield i)
      S.addEntry("LAZY>RESULT:UNSAT,BLOCKINGCLAUSES:" + bcCount)
      (ccu.Result.UNSAT, None)
    }
  }

  override def getStat(result : ccu.Result.Result) = {
    "LAZY>RESULT:" + result + ",BLOCKINGCLAUSES:" + bcCount
  }

  def unsatCoreAux(problem : CCUSimProblem, timeout : Int) = {
    lastUnsatCore
  }
}
