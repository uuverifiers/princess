package ccu;

import org.sat4j.tools.GateTranslator
import org.sat4j.minisat.SolverFactory
import org.sat4j.specs.ISolver
import org.sat4j.core.VecInt

import scala.collection.mutable.{Set => MSet}


class LazySolver[TERM, FUNC](timeoutChecker : () => Unit, 
                              maxSolverRuntime : Long)  
    extends CCUSolver[TERM, FUNC](timeoutChecker, maxSolverRuntime) {

  // We automatically calculate unsatCore
  var lastUnsatCore = List() : Seq[Int]

  // minimises DI s.t. what remains is a set of inequalities
  // s.t. if any one of them is removed, the goals can be
  // fulfilled using functions.
  
  // This is inexact! For example, given a != b, b != c, c != d, we get
  // that a ~= c, b ~= d, d ~= a (where ~= is "could be equal"), this
  // by transitivity (in some cases) yields that a = b = c = d

  override def solveaux() : ccu.Result.Result = {
    Timer.measure("Lazy.solve") {
      // Initialize problem and some useful values
      val terms = problem.terms
      val domains = problem.domains
      val bits = util.binlog(terms.length)


      // Reset and add default stuff
      this.reset

      // Shows what bits are used to represent value of terms
      val assignments = createAssignments(terms)

      // As long as the model is SAT, we can search for more solutions
      // Added for timing reasons
      def KeepOnGoing() = {
        var result = false 
        Timer.measure("SOLVE.SAT4J") {
          result = solver.isSatisfiable()
        }
        result
      }

      // Used to store what bits are equivalent to term equal term
      val teqt =
        Array.ofDim[Int](problem.terms.length, problem.terms.length)
      for (i <- 0 until problem.terms.length;
        j <- 0 until problem.terms.length)
        teqt(i)(j) = -1

      // Keeps track whether a subproblem has triggered UNSAT
      val blockingProblem = Array.ofDim[Boolean](problem.count)

      while (KeepOnGoing()) {
        timeoutChecker()

        val (termAss, intAss) = modelToAss(assignments, solver.model)


        // If all problems are SAT, then we are done
        var allSat = true

        // Check each problem one by one, adding blocking clauses
        // if any of the are UNSAT by this model
        var p = 0

        while (allSat && p < problem.count) {
          // Check if this IS a solution (exact check!)
          val cp = problem.problems(p)
          val verified = verifySolution[Int, Int](terms, intAss, cp.funEqs, cp.goal)

          if (!verified) {
            blockingProblem(p) = true

            // If not, we have to find a new model, but we should add a blocking
            // clause to not get the same model again
            allSat = false

            // Find out DI (i.e. expand diseq by using FP calculation)
            // this gives a lower bound on inequalities (i.e. inequalities)
            // that MUST hold

            // TODO: Use problem.dq?
            val DQ = new Disequalities(problem.terms.length, problem.problems(p).funEqs, timeoutChecker)

            // val sets = MSet() : MSet[Set[Int]]
            // for (t <- problem.terms)
            //   sets += Set(t)

            // val newSets = util.CC[Int, Int](sets, problem.problems(p).funEqs, intAss.toList)
            val uf = util.CCunionFind[Int, Int](problem.terms, 
              problem.problems(p).funEqs, intAss.toList)

            // def set(t : Int) : Set[Int] = {
            //   for (s <- newSets)
            //     if (s contains t)
            //       return s
            //   throw new Exception("No set contains t?")
            // }

            for (s <- problem.terms; t <- problem.terms;
              if (s <= t); if (uf(s) == uf(t))) {
              // diseq(s*problem.terms.length + t) = 1
              // diseq(t*problem.terms.length + s) = 1
              DQ.cascadeRemoveDQ(s, t)
            }

            // Now we minimize DI to only contain "relevant" inequalities
            DQ.minimise(problem.problems(p).goal)
            
            val minDI = DQ.getINEQ()

            // The blocking clause states that one of the inequalities
            // in minDI must be false (i.e. equality must hold)

            // Remove all "base" inequalities, since they will always be there
            // no need trying to satisfy those
            // println("LAZY: blockingClause: " + minDI.mkString(", "))
            // println("LAZY: baseDI: ")
            // println(problem.baseDI(p).map(x => x.mkString(" ")).mkString("\n"))
            val blockingClause =
              (for ((s,t) <- minDI) yield {
                // (for ((s,t) <- minDI;
                // if (problem.baseDI(p)(s)(t) != 0)) yield {
                if (teqt(s min t)(s max t) == -1) {
                  val newT =
                    termEqTermAux(
                      assignments(s),
                      assignments(t))
                  teqt(s min t)(s max t) = newT
                }
                // println("\t " + (s min t) + " != " + (s max t) + " [" + (teqt(s min t)(s max t)) + "]")
                teqt(s min t)(s max t)
              }).toArray

            try {
              // println("Adding blockingClause: " + blockingClause.mkString(" "))
              solver.addClause(new VecInt(blockingClause))
            } catch {
              case _ : Throwable => { 
                // println("EXCEPTION!")
                return ccu.Result.UNSAT 
              }
            }
          }
          p += 1
        }

        if (allSat) {
          model = Some(termAss)
          return ccu.Result.SAT
        }
      }

      // UNSAT
      lastUnsatCore = 
        (for (i <- 0 until problem.count; if (blockingProblem(i))) 
        yield i)
      ccu.Result.UNSAT
    }
  }

  def unsatCoreAux(timeout : Int) = {
    lastUnsatCore
  }
}
