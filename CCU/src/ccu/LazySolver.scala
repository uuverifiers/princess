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
  var lastUnsatCore = List() : List[Int]

  // minimises DI s.t. what remains is a set of inequalities
  // s.t. if any one of them is removed, the goals can be
  // fulfilled using functions.
  
  // This is inexact! For example, given a != b, b != c, c != d, we get
  // that a ~= c, b ~= d, d ~= a (where ~= is "could be equal"), this
  // by transitivity (in some cases) yields that a = b = c = d
  def minimiseDI(DI : Array[Array[Int]],
    functions : List[(FUNC, List[Int], Int)],
    goals : List[List[(Int, Int)]]) : List[(Int, Int)] = {
    Timer.measure("Lazy.minimiseDI") {

      val DQ = new Disequalities[FUNC](DI, functions, timeoutChecker)

      // Go through all disequalities
      // We try to remove disequalities one by one
      Timer.measure("MIN.Loop") {
        for (i <- 0 until DI.length; j <- 0 until DI.length;
          if (i < j); if (!DQ(i, j))) {
          timeoutChecker()

          Timer.measure("MIN.cascadeRemove") {
            DQ.cascadeRemoveDQ(i, j)
          }

          // Still UNSAT? Propagate Changes
          var sat = false
          Timer.measure("MIN.SAT4J") {
            sat = DQ.satisfies(goals)
          }

          if (!sat) {
            DQ.setBase()
          } else {
            DQ.restore()
          }
        }
      }

      DQ.getINEQ()
    }
  }


  override def solve() : ccu.Result.Result = {
    Timer.measure("Lazy.solve") {
      // Initialize problem and some useful values
      val terms = problem.allTerms
      val domains = problem.allDomains
      val bits = util.binlog(terms.length)


      // Reset and add default stuff
      solver.reset()
      solver.addClause(new VecInt(Array(ONEBIT)))
      solver.addClause(new VecInt(Array(-ZEROBIT)))

      // Shows what bits are used to represent value of terms
      val assignments = createAssignments(terms)

      // As long as the model is SAT, we can search for more solutions
      def KeepOnGoing() = {
        var result = false 
        Timer.measure("SOLVE.SAT4J") {
          result = solver.isSatisfiable()
        }
        result
      }

      // Used to store what bits are equivalent to term equal term
      val teqt =
        Array.ofDim[Int](problem.allTerms.length, problem.allTerms.length)
      for (i <- 0 until problem.allTerms.length;
        j <- 0 until problem.allTerms.length)
        teqt(i)(j) = -1

      // Keeps track whether a subproblem has triggered UNSAT
      val blockingProblem = Array.ofDim[Boolean](problem.count)

      while (KeepOnGoing()) {
        timeoutChecker()
        // Convert the model to a more convenient format
        var termAss = Map() : Map[TERM, TERM]
        var intAss = Map() : Map[Int, Int]

        Timer.measure("SOLVE.createAss2") {
          // If bit B is true, bitArray(bitMap(B)) should be true
          var bitMap = Map() : Map[Int, List[Int]]

          // Term T can find its bits in resultMap(T)
          var resultMap = Map() : Map[Int, List[Int]]

          // Prune all bits that are not with var ass and put in bitArray
          var bitArray = Array.ofDim[Boolean](terms.length * problem.bits)

          // Current position in bitArray
          var curPos = 0

          for ((term, bits) <- assignments) {
            val newResult = 
              (for (i <- 0 until bits.length) yield {
                val newList = curPos :: (bitMap.getOrElse(bits(i), List()))
                bitMap += (bits(i) -> newList)
                curPos += 1
                (curPos - 1)
              }).toList
            resultMap += term -> newResult
          }

          for (i <- solver.model) {
            val newVal = i >= 0
            for (b <- bitMap.getOrElse(Math.abs(i), List()))
              bitArray(b) = newVal
          }

          def bitToInt2(bits : List[Int]) = {
            var curMul = 1
            var curVal = 0
            for (b <- bits) {
              if (bitArray(b))
                curVal += curMul
              curMul *= 2
            }
            curVal
          }

          for (t <- terms) {
            val iVal = bitToInt2(resultMap(t))
            termAss += (problem.intMap(t) -> problem.intMap(iVal))
            intAss += (t -> iVal)
          }
        }

        // If all problems are SAT, then we are done
        var allSat = true

        // Check each problem one by one, adding blocking clauses
        // if any of the are UNSAT by this model
        var p = 0

        while (allSat && p < problem.count) {
          // Check if this IS a solution (exact check!)
          var verified = false
          Timer.measure("SOLVE.verify") {
            verified = verifySolution[Int, FUNC](terms, intAss, problem.functions(p), problem.goals(p))
          }

          if (!verified) {
            blockingProblem(p) = true

            // If not, we have to find a new model, but we should add a blocking
            // clause to not get the same model again
            allSat = false

            // Find out DI (i.e. expand diseq by using FP calculation)
            // this gives a lower bound on inequalities (i.e. inequalities)
            // that MUST hold
            // diseq(s)(t) Contains a 1 if terms s and t ARE equal (exact)
            var minDI = List() : List[(Int, Int)]
            Timer.measure("SOLVE.findMin") {
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
              minDI = minimiseDI(DI, problem.functions(p), problem.goals(p))
            }


            Timer.measure("SOLVE.addBlockingClause") {

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
                // println("blockingClause: " + blockingClause.mkString(" "))
                solver.addClause(new VecInt(blockingClause))
              } catch {
                case _ : Throwable => { return ccu.Result.UNSAT }
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
        yield i).toList
      ccu.Result.UNSAT
    }
  }

  def unsatCoreAux(timeout : Int) = {
    lastUnsatCore
  }
}


