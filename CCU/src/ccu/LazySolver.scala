package ccu;

import org.sat4j.tools.GateTranslator
import org.sat4j.minisat.SolverFactory
import org.sat4j.specs.ISolver
import org.sat4j.core.VecInt

import scala.collection.mutable.{Set => MSet}


class LazySolver[TERM, FUNC]() 
    extends CCUSolver[TERM, FUNC] {


  // minimises DI s.t. what remains is a set of inequalities
  // s.t. if any one of them is removed, the goals can be
  // fulfilled using functions.
  
  // This is inexact! For example, given a != b, b != c, c != d, we get
  // that a ~= c, b ~= d, d ~= a (where ~= is "could be equal"), this
  // by transitivity (in some cases) yields that a = b = c = d
  def minimiseDI(DI : Array[Array[Int]],
    functions : List[(FUNC, List[Int], Int)],
    goals : List[List[(Int, Int)]]) = {
    Timer.measure("Lazy.minimiseDI") {

      def isSAT(newDI : Array[Array[Int]]) = {
        // println("BEFORE DISEQUALITY CHECK:")
        // println(newDI.map(x => x.mkString(" ")).mkString("\n"))

        util.disequalityCheck(newDI, functions)
        // println("AFTER DISEQUALITY CHECK (ORG):")
        // println(newDI.map(x => x.mkString(" ")).mkString("\n"))

        var satisfiable = false

        for (subGoal <- goals) {
          var subGoalSat = true

          var allPairsTrue = true
          for ((s,t) <- subGoal) {
            if (newDI(s)(t) == 0) {
              allPairsTrue = false
            }

            if (!allPairsTrue)
              subGoalSat = false
          }
          if (subGoalSat)
            satisfiable = true
        }
        satisfiable
      }

      var tmpDI = Array.ofDim[Int](DI.length, DI.length)

      val DQ = new Disequalities(DI, functions)


      for (i <- 0 until DI.length; j <- 0 until DI.length;
        if (i < j); if (DI(i)(j) == 0)) {

        // Restore tmpDI to be equal to DI
        for (i <- 0 until DI.length; j <- 0 until DI.length)
          tmpDI(i)(j) = DI(i)(j)

        // Try removing one disequality
        tmpDI(i)(j) = 1
        tmpDI(j)(i) = 1

        // Still UNSAT? Propagate Changes
        if (!isSAT(tmpDI)) {
          for (i <- 0 until DI.length; j <- 0 until DI.length;
            if (tmpDI(i)(j) == 1))
            DI(i)(j) = tmpDI(i)(j)
        }
      }
      
      (for (i <- 0 until DI.length; j <- 0 until DI.length;
        if (i < j); if (DI(i)(j) == 0)) yield
        (i,j)).toList
    }
  }


  override def solve() : ccu.Result.Result = {
    Timer.measure("Lazy.solve") {
      println("\nLAZY: Using Lazy solver")

      // Initialize problem and some useful values
      val terms = problem.allTerms
      val domains = problem.allDomains

      // Shows what bits are used to represent value of terms
      val bits = util.binlog(terms.length)

      // Reset and add default stuff
      solver.reset()
      solver.addClause(new VecInt(Array(ONEBIT)))
      solver.addClause(new VecInt(Array(-ZEROBIT)))

      val assignments = createAssignments(terms)

      // Just keeping track of how many candidate solutions we have checked
      var tries = 0

      // As long as the model is SAT, we can search for more solutions

      def KeepOnGoing() = {
        var result = false 
        Timer.measure("Lazy.SAT4J") {
          result = solver.isSatisfiable()
        }
        result
      }

      while (KeepOnGoing()) {
        println(Timer)
        // Convert the model to a more convenient format
        var termAss = Map() : Map[TERM, TERM]
        var intAss = Map() : Map[Int, Int]
        for (t <- terms) {
          val iVal = bitToInt(assignments(t))
          termAss += (problem.intMap(t) -> problem.intMap(iVal))
          intAss += (t -> iVal)
        }

        tries += 1
        println("\n\nCandidate solution (TRY: " + tries + "): " + intAss)

        // If all problems are SAT, then we are done
        var allSat = true

        // Check each problem one by one, adding blocking clauses
        // if any of the are UNSAT by this model
        var p = 0
        while (allSat && p < problem.count) {
          // Check if this IS a solution (exact check!)
          if (!verifySolution[Int, FUNC](terms, intAss, problem.functions(p), problem.goals(p))) {

            // If not, we have to find a new model, but we should add a blocking
            // clause to not get the same model again
            allSat = false

            // Find out DI (i.e. expand diseq by using FP calculation)
            // this gives a lower bound on inequalities (i.e. inequalities)
            // that MUST hold
            // diseq(s)(t) Contains a 1 if terms s and t ARE equal (exact)
            val diseq = Array.ofDim[Int](problem.allTerms.length, problem.allTerms.length)

            val sets = MSet() : MSet[Set[Int]]
            for (t <- problem.allTerms)
              sets += Set(t)

            val newSets = util.CC[FUNC, Int](sets, problem.functions(p), intAss.toList)

            def set(t : Int) : Set[Int] = {
              for (s <- newSets)
                if (s contains t)
                  return s
              throw new Exception("No set contains t?")
            }

            for (s <- problem.allTerms; t <- problem.allTerms;
              if (s <= t); if (set(s) == set(t))) {
              diseq(s)(t) = 1
              diseq(t)(s) = 1
            }

            val DI = util.disequalityCheck(diseq, problem.functions(p))

            // Now we minimize DI to only contain "relevant" inequalities
            val minDI = minimiseDI(DI, problem.functions(p), problem.goals(p))



            // The blocking clause states that one of the inequalities
            // in minDI must be false (i.e. equality must hold)

            // Remove all "base" inequalities, since they will always be there
            // no need trying to satisfy those
            // println("LAZY: blockingClause: " + minDI.mkString(", "))
            val blockingClause =
              (for ((s,t) <- minDI;
                if (problem.baseDI(p)(s)(t) != 0)) yield {
                termEqTermAux(
                  assignments(s),
                  assignments(t))
              }).toArray

            try {
              solver.addClause(new VecInt(blockingClause))
            } catch {
              case _ : Throwable => { return ccu.Result.UNSAT }
            }
          }
          p += 1
        }
        if (allSat) {
          println("LAZY: SAT: " + intAss)
          return ccu.Result.SAT
          // return Some(termAss)
        }
      }

      // UNSAT
      ccu.Result.UNSAT
    }
  }

  def minUnsatCore() = {
    Timer.measure("Lazy.minUnsatCore") {
      (0 until problem.count).toList
    }
  }
}


