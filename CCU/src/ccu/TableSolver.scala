package ccu;

import org.sat4j.tools.GateTranslator
import org.sat4j.minisat.SolverFactory
import org.sat4j.specs.ISolver
import org.sat4j.core.VecInt

import scala.collection.mutable.{Set => MSet}
import scala.collection.mutable.{Map => MMap}
import scala.collection.mutable.ListBuffer


class TableSolver[TERM, FUNC](timeoutChecker : () => Unit, 
                              maxSolverRuntime : Long)  
    extends CCUSolver[TERM, FUNC](timeoutChecker, maxSolverRuntime) {


  var tablesComplete = false
  var tables = List() : List[Table[FUNC]]

  def solveTable() : (Option[Array[Int]], Map[Int, List[Int]]) = {
    Timer.measure("Table.solveTable") {
      // We have p problems, and we are dealing with the simultaneous problem,
      // i.e. every problem must be solvable
      var allGoalPossible = true

      val assignments = createAssignments(problem.allTerms)

      val diseqedGoals =
        (for (p <- 0 until problem.count) yield {
          // This particular problem consists of subgoals,
          // one of the subgoals must be solvable for the
          // whole problem to be possible
          (for (gs <- problem.goals(p)) yield {
            // A subgoal consists of pairs of terms,
            // all of the must be unifiable for this
            // subgoal to be possible.

            var allUnifiable = true
            for ((s,t) <- gs) {
              if (problem.diseq(p)(s)(t) == 0)
                allUnifiable = false
            }

            (gs, allUnifiable)
          }).filter(x => x._2).map(x => x._1).toList
        }).toList


      if (diseqedGoals contains List()) {
        // println("\tDISEQUALITY CHECK DEEMS PROBLEM IMPOSSIBLE")
        return (None, Map())
      }

      tables =
        (for (i <- 0 until problem.count) yield {
          new Table[FUNC](problem.bits, alloc, gt, solver,
            problem.terms(i), problem.domains(i),
            problem.functions(i), ZEROBIT, ONEBIT, problem.diseq(i))
        }).toList


      solver.addClause(new VecInt(Array(-ZEROBIT)))
      solver.addClause(new VecInt(Array(ONEBIT)))

      // MAIN SOLVE LOOP
      var cont = true
      var model = None : Option[Array[Int]]
      val bits = problem.bits
      val terms = problem.allTerms
      val domains = problem.allDomains
      val problemCount = problem.count
      val goals = problem.goals

      // Create Initial Column

      def termAssIntAux(i : Int) = {
        var curVal = i

        for (b <- 0 until bits) yield {
          if (curVal % 2 == 1) {
            curVal -= 1
            curVal /= 2
            ONEBIT
          } else {
            curVal /= 2
            ZEROBIT
          }
        }
      }

      def termEqIntAux(bitList : List[Int], i : Int) : Int = {
        Timer.measure("termEqInt") {
          var curVal = i

          val lits =
            (for (b <- bitList) yield {
              if (curVal % 2 == 1) {
                curVal -= 1
                curVal /= 2
                b
              } else {
                curVal /= 2
                -b
              }
            }).toArray

          val eqBit = alloc.alloc(1)
          gt.and(eqBit, new VecInt(lits))
          eqBit
        }
      }

      for (p <- 0 until problemCount)
        tables(p).addInitialColumn(assignments)

      for (p <- 0 until problemCount) {
        tables(p).addDerivedColumn(timeoutChecker)
      }

      while (cont) {
        timeoutChecker()

        val goalConstraints =
          for (p <- 0 until problemCount; if (!goals(p).isEmpty)) yield
            tables(p).addGoalConstraint(goals(p))
         
        Timer.measure("isSat") {
          // solver.setTimeoutMs(maxSolverRuntime)
          if (solver.isSatisfiable()) {
            for (gc <- goalConstraints)
              solver.removeConstr(gc)
            model = Option(solver.model)
            cont = false
          } else {
            for (gc <- goalConstraints)
              solver.removeConstr(gc)

            def CCPerTable() : Boolean = {
              // Check table per table
              for (p <- 0 until problemCount) {
                val cc =
                  tables(p).addCompletionConstraint()

                // solver.setTimeoutMs(maxSolverRuntime)
                val sat = solver.isSatisfiable()
                solver.removeConstr(cc)

                if (sat)
                  return true
              }
              false
            }

            def CCAllTables() : Boolean = {
              val ccs =
                for (p <- 0 until problemCount) yield
                  tables(p).addCompletionConstraint()

              // solver.setTimeoutMs(maxSolverRuntime)
              val sat = solver.isSatisfiable()
              for (cc <- ccs)
                solver.removeConstr(cc)

              sat
            }

            def CCV() : Boolean = {
              val ccs =
                for (p <- 0 until problemCount) 
                yield tables(p).addVConstraint



              val retVal = 
              if (ccs contains None) {
                false
              } else {
                solver.isSatisfiable()
              }

              for (cc <- ccs; if cc.isDefined)
                solver.removeConstr(cc.get)

              retVal
            }


            Timer.measure("completionConstraint_" + tables(0).currentColumn + "_columns") {
              val moreInfo = CCV()

              if (!moreInfo) {
                tablesComplete = true
                model = None
                cont = false
              } else {
                for (p <- 0 until problemCount)
                  tables(p).addDerivedColumn(timeoutChecker)
              }
            }
          }
        }
      }

      // TODO: Change if differents rows
      Timer.measure("Columns_" +
        (for (p <- 0 until problemCount)
        yield tables(p).currentColumn).mkString("[", " ", "]")) { true }

      (model, assignments)
    }
  }

  // Given a list of domains, goals, functions, see if there is a solution to
  // the simultaneous problem.
  override def solve() : ccu.Result.Result = {
    Timer.measure("Table.solve") {
      // Reset and add default stuff
      reset
      solver.addClause(new VecInt(Array(ONEBIT)))
      solver.addClause(new VecInt(Array(-ZEROBIT)))
      tablesComplete = false

      val terms = problem.allTerms
      val domains = problem.domains
      val goals = problem.goals
      val functions = problem.functions

      solveTable() match {
        // TODO: Some(m), m unused?
        case (Some(m), assignments) => {
          var assMap = Map() : Map[TERM, TERM]
          var intAss = Map() : Map[Int, Int]
          for (t <- problem.allTerms) {
            val iVal = bitToInt(assignments(t))
            intAss += (t -> iVal)
            assMap += (intToTerm(t) -> intToTerm(iVal))
          }

          model = Some(assMap)
          problem.intAss = intAss
          problem.result = Some(ccu.Result.SAT)
          ccu.Result.SAT
        }

        case (None, _) =>  {
          problem.result = Some(ccu.Result.UNSAT)
          ccu.Result.UNSAT
        }
      }
    }
  }

  def solveAgain() : Boolean = {
    Timer.measure("Table.solveAgain") {
      if (problem.goals.flatten.flatten.isEmpty) 
        throw new Exception("SolveAgain emptyproblem!")

      var retval = false : Boolean

      if (tablesComplete) {
        val goals = problem.goals

        val goalConstraints = 
          for (p <- 0 until problem.count; if (!goals(p).flatten.isEmpty)) yield {
            tables(p).addGoalConstraint(goals(p))
          }

        retval =  solver.isSatisfiable()

        for (gc <- goalConstraints) {
          solver.removeConstr(gc)
        }
      } else {
        solveTable() match {
          case (Some(_), _) => retval = true
          case (None, _) => retval = false
        }
      }

      retval
    }
  }



  // PRE: Call after solve returns UNSAT
  def unsatCoreAux(timeout : Int) : List[Int] = {
    solver.setTimeoutMs(timeout)
    Timeout.withTimeoutMillis(timeout) {
      val unsatCore = ListBuffer() : ListBuffer[Int]

      if (!problem.result.isDefined)
        throw new Exception("unsatCore on without previous solve call")
      
      if (problem.result.get != ccu.Result.UNSAT)
        throw new Exception("unsatCore on SAT solution")

      for (p <- 0 until problem.count)
        problem.removeGoal(p)

      var curProb = 0
      unsatCore += curProb
      problem.restoreGoal(curProb)

      def addProblem = {
        curProb += 1
        if (curProb < problem.count) {
          unsatCore += curProb
          problem.restoreGoal(curProb)
        }
      }

      while (curProb < problem.count) {
        Timeout.check
        timeoutChecker()

        if (solveAgain()) {
          // If the problem is SAT, we need one more sub-problem
          addProblem
        } else {
          // Make sure that tables 0..p are complete,
          // if NOT, we have to add columns
          // if IS, we have an unsat core!

          val ccs =
            for (p <- 0 to curProb) yield
              tables(p).addVConstraintAux match {
                case (Some(cc), bits) => (Some(cc), bits)
                case (None, _) => {
                  (None, List())
                }
              }

          // Do we need extra columns?
          val addColumn =
            if (ccs.filter(x => x._1.isDefined).isEmpty) {
              false
            } else {
              solver.isSatisfiable()
            }

          for (cc <- ccs; if cc._1.isDefined) {
            solver.removeConstr(cc._1.get)
          }

          if (addColumn) {
            // if YES - Add and try again
            for (p <- 0 to curProb)
              tables(p).addDerivedColumn(timeoutChecker)
          } else {
            // if NO - unsat core achieved!
            return unsatCore.toList
          }
        }
      }
      throw new Exception("TableSolver: Entire problem is not UNSAT?")
    }{
      return (0 until problem.count).toList
    }
  }
}


class Table[FUNC](val bits : Int, alloc : Allocator,
  gt : GateTranslator, solver : ISolver, val terms : List[Int],
  domains : Map[Int, Set[Int]], functions : List[(FUNC, List[Int], Int)],
  ZEROBIT : Int, ONEBIT : Int, diseq : Array[Array[Int]]) {

  val columns = ListBuffer() : ListBuffer[MMap[Int, List[Int]]]
  var currentColumn = 0

  // Access Table[Column][Row]
  def apply(term : (Int, Int)) = {
    val (col, row) = term
    columns(col)(row)
  }

  // USE AFTER solved
  def printTable {

    def bitToInt(bits : List[Int]) : Int = {
      var curMul = 1
      var curVal = 0
      for (b <-bits) {
        if (solver.model contains b)
          curVal += curMul
        curMul *= 2
      }
      curVal
    }

    println("<-----" + ("---" * currentColumn) + "-->")
    for (t <- terms) {
      print(t + ">\t")
      for (c <- 0 to currentColumn) {
        val i = bitToInt(this((c, t)))
        print(" " + i)
      }
      println
    }
    printTableStats
  }

  def printTableStats {
    println("<#####" + ("###" * 3) + "##>")
    println("currentColum: " + currentColumn)
    for (t <- terms)
      println(t + " := {" + domains(t).mkString(", ") + "}")
    println("functions:")
    for (f <- functions)
      println("\t" + f)
    println("<-----" + ("---" * 3) + "-->")
  }

  //
  //  TERM EQUALITY FUNCTION
  //

  // C[t] == i
  def termEqInt(term : (Int, Int), i : Int) : Int = {
    Timer.measure("termEqInt") {
      var curVal = i

      val lits =
        (for (t <- this(term)) yield {
          if (curVal % 2 == 1) {
            curVal -= 1
            curVal /= 2
            t
          } else {
            curVal /= 2
            -t
          }
        }).toArray

      val eqBit = alloc.alloc(1)
      gt.and(eqBit, new VecInt(lits))
      eqBit
    }
  }

  // C[t1] == C[t2]
  def termEqTerm(term1 : (Int, Int), term2 : (Int, Int)) : Int = {
    Timer.measure("termEqTerm") {
      val term1Bits = this(term1)
      val term2Bits = this(term2)

      val maxBits = term1Bits.length max term2Bits.length

      val term1BitsPadded = term1Bits.padTo(maxBits, ZEROBIT)
      val term2BitsPadded = term2Bits.padTo(maxBits, ZEROBIT)

      // TODO: Could be optimised (by not doing padding...)
      val eqBits =
        (for ((t1b, t2b) <- term1BitsPadded zip term2BitsPadded) yield {
          val tmpBit = alloc.alloc(1)
          gt.iff(tmpBit, new VecInt(Array(t1b, t2b)))
          tmpBit
        }).toArray

      val eqBit = alloc.alloc(1)
      gt.and(eqBit, new VecInt(eqBits))
      eqBit
    }
  }

  // C[t1] > C[t2]
  def termGtTerm(term1 : (Int, Int), term2 : (Int, Int)) : Int = {
    Timer.measure("termGtTerm") {
      val (c1, t1) = term1
      val (c2, t2) = term2

      val term1Bits = this(c1, t1)
      val term2Bits = this(c2, t2)
      val maxBits = term1Bits.length max term2Bits.length

      // Make the reversed since we are studying from most significant bit
      val term1BitsPadded = term1Bits.padTo(maxBits, ZEROBIT).reverse
      val term2BitsPadded = term2Bits.padTo(maxBits, ZEROBIT).reverse

      // e_bits[b]: bit (bits-b) of i and j are equal
      var e_bits = List() : List[Int]
      // for (b <- 1 to maxBits) yield {
      for ((t1b, t2b) <- term1BitsPadded zip term2BitsPadded) {

        // term1[bits - b] = term2[bits - b]
        val bitsEq = alloc.alloc(1)
        gt.iff(bitsEq, new VecInt(Array(t1b, t2b)))

        if (e_bits.isEmpty) {
          e_bits = e_bits :+ bitsEq
        } else {
          val prevEq = alloc.alloc(1)
          gt.and(prevEq, e_bits.last, bitsEq)
          e_bits = e_bits :+ prevEq
        }
      }

      var m_bits = List() : List[Int]

      // m_bits[b]: bits [bits..(bits-b)] of i are greater than j
      // for (b <- 1 to bits) {
      for (b <- 0 until maxBits) {
        val bit_gt = alloc.alloc(1)
        gt.and(bit_gt, term1BitsPadded(b), -term2BitsPadded(b))

        if (m_bits.isEmpty) {
          m_bits = m_bits :+ bit_gt
        } else {
          val prev_eq = e_bits(b-1)

          // Option1: All prev bits are eq and this is greater
          val opt1 = alloc.alloc(1)
          gt.and(opt1, prev_eq, bit_gt)

          // Option2: Term1 was already greater than Term2
          val opt2 = m_bits(b-1)

          val m = alloc.alloc(1)
          gt.or(m, new VecInt(Array(opt1, opt2)))
          m_bits = m_bits :+ m
        }
      }
      m_bits.last
    }
  }

  def addInitialColumn(assignments : Map[Int, List[Int]]) {
    val newColumn =
      MMap() ++ (for (t <- terms) yield
        (t, assignments(t))).toMap

    columns += newColumn
  }

  def addDerivedColumn(timeoutChecker : () => Unit) = {
    Timer.measure("addDerivedColumn") {
      // For all pairs of functions with identical function symbols and
      // different results,form a 3-tuple of (v_ij, (arg_i, s_i), (arg_j, s_j))
      currentColumn += 1

      val startBit = alloc.alloc(terms.length * bits)

      val newColumn =
        MMap() ++ (List.tabulate(terms.length)(x => {
          (terms(x), List.tabulate(bits)(y => startBit + x*bits + y))
        })).toMap

      columns += newColumn

      val eqBits = Array.tabulate(terms.length, terms.length)( (x, y) => -1)

      // termToIndex
      val tTI = (for (t <- terms) yield (t, terms indexOf t)).toMap

      def unifiable(args1 : List[Int], args2 : List[Int]) : Boolean = {
        for ((a1, a2) <- (args1 zip args2)) {
          if (diseq(a1)(a2) == 0)
            return false
        }
        return true
      }


      val V =
        for ((f_i, args_i, s_i) <- functions;
          (f_j, args_j, s_j) <- functions;
          if (f_i == f_j && s_i != s_j && unifiable(args_i, args_j))) yield {
          val argBits =
            (for (i <- 0 until args_i.length) yield {
              val t1 = args_i(i) min args_j(i)
              val t2 = args_i(i) max args_j(i)
              if (eqBits(tTI(t1))(tTI(t2)) == -1)
                eqBits(tTI(t1))(tTI(t2)) =
                  termEqTerm((currentColumn-1, args_i(i)),
                    (currentColumn-1,args_j(i)))

              eqBits(tTI(t1))(tTI(t2))
            }).toArray

          // argBit <=> C_p[args_i] = C_p[args_j]
          val argBit = 
            if (argBits.isEmpty) {
              // No arguments (i.e. f() = a && f() = b is trivial equality)
              ONEBIT
            } else {
              val tmp = alloc.alloc(1)
              gt.and(tmp, new VecInt(argBits))
              tmp
            }

          // gtBit <=> C_p[s_i] > C_p[s_j]
          val gtBit = termGtTerm((currentColumn-1, s_i), (currentColumn-1, s_j))

          // vBit <=> args_i = args_j ^ s_i > s_j
          val vBit = alloc.alloc(1)
          gt.and(vBit, argBit, gtBit)

          (vBit, (args_i, s_i), (args_j, s_j))
        }




      for (t <- terms) {
        // --- CASE0: Not a representing term, following a rowless bit ---
        timeoutChecker()
        val neqBits =
          (for (tt <- terms) yield {
            -termEqInt((currentColumn-1, t), tt)
          }).toArray

        val diffBit = alloc.alloc(1)
        gt.and(diffBit, new VecInt(neqBits))

        // Force identity
        val idBit = termEqTerm((currentColumn-1, t), (currentColumn, t))
        solver.addClause(new VecInt(Array(-diffBit, idBit)))

        // --- CASE1: Not a representing term ---

        for (tt <- terms; if t != tt; if (diseq(t)(tt) != 0)) {
          val eqBit = termEqInt((currentColumn-1, t), tt)
          val asBit = termEqTerm((currentColumn, t), (currentColumn, tt))

          // C_p[t] = tt ==> C_c[t] = C_c[tt]
          solver.addClause(new VecInt(Array(-eqBit, asBit)))
        }

        // --- CASE2: Representing term ---

        // is this term allowed to be identity

        val noVBits =
          (for ((vBit, (args_i, s_i), (args_j, s_j)) <- V) yield {

            // C_p[s_i] = t
            val eqBit = termEqInt((currentColumn-1, s_i), t)
            val ineqBit = alloc.alloc(1)
            gt.not(ineqBit, eqBit)

            val noVBit = alloc.alloc(1)

            // noVBit <=> !V ^ C_p[s_i] != t
            gt.or(noVBit, new VecInt(Array(ineqBit, -vBit)))
            noVBit
          }).toArray


        // vFalseBit <=> No V is true
        val vFalseBit = alloc.alloc(1)
        gt.and(vFalseBit, new VecInt(noVBits))



        // C_c[t] = t
        val eqBit = termEqInt((currentColumn, t), t)

        val identityBit = alloc.alloc(1)
        gt.and(identityBit, vFalseBit, eqBit)

        // Lets add a new condition:
        // -Require that all to be allowed to "use" v (in V)
        // all v' s.t. v' < v, and applicable to row r
        // must be set to false (i.e. use the v:s in a
        // increasing (and deterministic) order)

        val funcBits =
          (for ((vBit, (args_i, s_i), (args_j, s_j)) <- V) yield {
            timeoutChecker()
            // C_p[s_i] = t
            val prevEqBit = termEqInt((currentColumn - 1, s_i), t)

            // C_c[t] = C_c[s_j]
            val curEqBit = termEqTerm((currentColumn, t), (currentColumn, s_j))

            // FORALL v2 < vBit : !(v2 ^ prevEqBit2) === (!v' v !prevEqBit2)
            val minVBits = 
              (for ((vBit2, (args_i2, s_i2), (args_j2, s_j2)) <- V;
                if (vBit2 < vBit)) yield {
                val prevEqBit2 = termEqInt((currentColumn - 1, s_i2), t)
                val minVBit = alloc.alloc(1)
                gt.or(minVBit, new VecInt(Array(-vBit2, -prevEqBit2)))
                minVBit
              }).toArray

            val mBit = alloc.alloc(1)
            gt.and(mBit, new VecInt(minVBits))

            val fBit = alloc.alloc(1)
            gt.and(fBit, new VecInt(Array(vBit, prevEqBit, curEqBit, mBit)))
            fBit
          }).toArray

        val functionalityBit = alloc.alloc(1)
        if (funcBits.length == 0) {      
          gt.gateFalse(functionalityBit)
        } else {
          gt.or(functionalityBit, new VecInt(funcBits))
        }

        // C_p[t] = t
        val isRepresentative = termEqInt((currentColumn-1, t), t)

        // C_p[t] = t => (C_c[t] = t v C_c[t] = s) for some functionality t = s
        // not representative OR allowed identity OR derived functionality
        solver.addClause(
          new VecInt(
            Array(-isRepresentative, identityBit, functionalityBit)))
      }
    }
  }

  // TODO: Make sure goal variables are removed at "POP"
  def addGoalConstraint(goals : List[List[(Int, Int)]]) = {
    val goalBits =
      (for (g <- goals; if (!g.isEmpty)) yield {
        val subGoals =
          (for ((s, t) <- g) yield {
            termEqTerm((currentColumn, s), (currentColumn, t))
          }).toArray
        val subGoal = alloc.alloc(1)
        gt.and(subGoal, new VecInt(subGoals))
        subGoal
      }).toArray

    solver.addClause(new VecInt(goalBits))
  }

  def addCompletionConstraint() = {
    Timer.measure("addCompletionConstraint") {
      val diff =
        (for (t <- terms)
        yield (-termEqTerm((currentColumn-1, t), (currentColumn, t)))).toArray
      
      solver.addClause(new VecInt(diff))
    }
  }

  def getCompletionConstraint() = {
    Timer.measure("getCompletionConstraint") {
      val diff =
        (for (t <- terms)
        yield (-termEqTerm((currentColumn-1, t), (currentColumn, t)))).toArray
      
      val cc = alloc.alloc(1)
      gt.or(cc, new VecInt(diff))
      cc
    }
  }

  def addGoalCompletionConstraint(goals : List[List[(Int, Int)]]) = {
    Timer.measure("addGoalCompletionConstraint") {
      val goalBits =
        (for (g <- goals) yield {
          val subGoals =
            (for ((s, t) <- g)
            yield termEqTerm((currentColumn, s), (currentColumn, t))).toArray
          
          val subGoal = alloc.alloc(1)
          gt.and(subGoal, new VecInt(subGoals))
          subGoal
        }).toArray

      val goalBit = alloc.alloc(1)
      gt.or(goalBit, new VecInt(goalBits))

      val diff =
        (for (t <- terms)
        yield (-termEqTerm((currentColumn-1, t), (currentColumn, t)))).toArray
      
      val solverClause = solver.addClause(new VecInt(goalBits ++ diff))
      (solverClause, goalBit)
    }
  }

  def getGoalCompletionConstraint(goals : List[List[(Int, Int)]]) = {
    Timer.measure("getGoalCompletionConstraint") {
      val goalBits =
        (for (g <- goals) yield {
          val subGoals =
            (for ((s, t) <- g)
            yield termEqTerm((currentColumn, s), (currentColumn, t))).toArray

          val subGoal = alloc.alloc(1)
          gt.and(subGoal, new VecInt(subGoals))
          subGoal
        }).toArray

      val goalBit = alloc.alloc(1)
      gt.or(goalBit, new VecInt(goalBits))

      val diff =
        for (t <- terms)
        yield (-termEqTerm((currentColumn-1, t), (currentColumn, t)))

      val gc = alloc.alloc(1)
      gt.or(gc, new VecInt(goalBits ++ diff))
      (gc, goalBit)
    }
  }

  def addVConstraintAux = {
    // termToIndex 
    // converts a term into its index in terms ...
    val tTI = (for (t <- terms) yield (t, terms indexOf t)).toMap

    // Returns true if args1 could equal args2
    def unifiable(args1 : List[Int], args2 : List[Int]) : Boolean = {
      for ((a1, a2) <- (args1 zip args2)) {
        if (diseq(a1)(a2) == 0)
          return false
      }
      return true
    }

    val eqBits = Array.tabulate(terms.length, terms.length)( (x, y) => -1)

    val V =
      for ((f_i, args_i, s_i) <- functions;
        (f_j, args_j, s_j) <- functions;
        if (f_i == f_j && s_i != s_j && unifiable(args_i, args_j))) yield {

        val argBits =
          (for (i <- 0 until args_i.length) yield {
            val t1 = args_i(i) min args_j(i)
            val t2 = args_i(i) max args_j(i)
            if (eqBits(tTI(t1))(tTI(t2)) == -1)
              eqBits(tTI(t1))(tTI(t2)) =
                termEqTerm((currentColumn, args_i(i)),
                  (currentColumn,args_j(i)))
            eqBits(tTI(t1))(tTI(t2))
          }).toArray

        // argBit <=> C_p[args_i] = C_p[args_j]
        val argBit =
          if (argBits.isEmpty) {
            // No arguments (i.e. f() = a && f() = b is trivial equality)
            ONEBIT
          } else {
            val tmp = alloc.alloc(1)
            gt.and(tmp, new VecInt(argBits))
            tmp
          }

        gt.and(argBit, new VecInt(argBits))

        // gtBit <=> C_p[s_i] > C_p[s_j]
        val gtBit = termGtTerm((currentColumn, s_i), (currentColumn, s_j))

        // vBit <=> args_i = args_j ^ s_i > s_j
        val vBit = alloc.alloc(1)
        gt.and(vBit, argBit, gtBit)

        vBit
      }

    if (V.isEmpty)
      (None, List())
    else
      (Some(solver.addClause(new VecInt(V.toArray))), V)
  }

  def addVConstraint = {
    val (ret, bits) = addVConstraintAux
    ret
  }
}
