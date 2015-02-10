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
    goals : List[List[(Int, Int)]]) : List[(Int, Int)] = {
    Timer.measure("Lazy.minimiseDI") {

      // println("DI: " + DI.map(x => x.mkString(" ")).mkString("\n"))
      // val DQ = new Disequalities[FUNC](DI, functions)
      val DQ2 = new Disequalities[FUNC](DI, functions)
      // println("DQ2:")
      // DQ2.doprint

      // Go through all disequalities
      // We try to remove disequalities one by one
      Timer.measure("MIN.Loop") {
        for (i <- 0 until DI.length; j <- 0 until DI.length;
          if (i < j); if (!DQ2(i, j))) {
          // var equal = false
          // equal = DQ.equalTo(DQ2)
          
          // if (equal) {
          //   println("EQUAL")
          //   // println("DQ")
          //   // DQ.print()
          //   // println("DQ2")
          //   // DQ2.doprint()
          // }

          // Try removing one disequality
          // println("PRUNING DQ")
          // println("\tremoving: " + ((i, j)))
          // DQ.unify(i, j)
          // DQ.pruneINEQ()

          Timer.measure("MIN.cascadeRemove") {
            DQ2.cascadeRemoveDQ(i, j)
          }

          // if (equal && !DQ.equalTo(DQ2))
          //   println(10 / 0)
          
          // Still UNSAT? Propagate Changes
          var sat = false
          sat = DQ2.satisfies(goals)

          if (!sat) {
            // DQ.setBase()
            DQ2.setBase()
          } else {
            // DQ.restore()
            // println("Restoring ...")
            DQ2.restore()
          }
        }
      }

      // Timer.measure("MIN.getINEQ") {
      // if (DQ.getINEQ() != DQ2.getINEQ())
      //   println(10/0)

      // println("RESULT:")
      // DQ2.doprint
      // println("\n\n\n")
      // problem.print("AFTERMINIMISE")
      // println("\n\n\n")
      DQ2.getINEQ()
    }
  }


  override def solve() : ccu.Result.Result = {
    Timer.measure("Lazy.solve") {
      var assignments = Map() : Map[Int, List[Int]]
      // Initialize problem and some useful values
        val terms = problem.allTerms
        val domains = problem.allDomains

      Timer.measure("SOLVE.Init") {
        // Shows what bits are used to represent value of terms
        val bits = util.binlog(terms.length)

        // Reset and add default stuff
        solver.reset()
        solver.addClause(new VecInt(Array(ONEBIT)))
        solver.addClause(new VecInt(Array(-ZEROBIT)))

        assignments = createAssignments(terms)
      }

      // Just keeping track of how many candidate solutions we have checked
      var tries = 0

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


      while (KeepOnGoing()) {
        // println(Timer)
        // Convert the model to a more convenient format
        var termAss = Map() : Map[TERM, TERM]
        var intAss = Map() : Map[Int, Int]

        // var termAss2 = Map() : Map[TERM, TERM]
        // var intAss2 = Map() : Map[Int, Int]
        // Timer.measure("SOLVE.createAss") {
        //   for (t <- terms) {
        //     var iVal = 0
        //     Timer.measure("SOLVE.createAss.bitToInt") {
        //       iVal = bitToInt(assignments(t))
        //     }
        //     Timer.measure("SOLVE.createAss.termAss+=") {
        //       termAss += (problem.intMap(t) -> problem.intMap(iVal))
        //     }
        //     Timer.measure("SOLVE.createAss.intAss+=") {
        //       intAss += (t -> iVal)
        //     }
        //   }
        // }

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


        tries += 1
        // println("\n\nCandidate solution (TRY: " + tries + "): " + intAss)

        // If all problems are SAT, then we are done
        var allSat = true

        // Check each problem one by one, adding blocking clauses
        // if any of the are UNSAT by this model
        var p = 0

        Timer.measure("SOLVE.Loop") {
          while (allSat && p < problem.count) {
            // Check if this IS a solution (exact check!)
            var verified = false
            Timer.measure("SOLVE.verify") {
              verified = verifySolution[Int, FUNC](terms, intAss, problem.functions(p), problem.goals(p))
            }

            if (!verified) {

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
        }

        if (allSat) {
          println("LAZY: SAT: " + intAss)
          model = Some(termAss)
          return ccu.Result.SAT
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


