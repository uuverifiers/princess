package ccu;

import org.sat4j.core._
import org.sat4j.specs._
import org.sat4j.minisat._
import org.sat4j.tools._

import Timer._

import scala.collection.mutable.{Map => MMap}
import scala.collection.mutable.{Set => MSet}
import scala.collection.mutable.{MutableList => MList}
import scala.collection.mutable.ListBuffer

class Allocator(init : Int) {
  var next = init

  def alloc(count : Int) = {
    val ret = next
    next = next + count
    ret
  }
}

class Problem[TERM, FUNC](
  val count : Int,
  val allTerms : List[Int],
  val allDomains : Map[Int, Set[Int]],
  val terms : List[List[Int]],
  val domains : List[Map[Int, Set[Int]]],
  var goals : List[List[List[(Int, Int)]]],
  val functions : List[List[(FUNC, List[Int], Int)]],
  val bits : Int,
  val diseq : List[Array[Array[Int]]],
  val termMap : Map[Int, TERM])
{ 

  // SubGoal removal variables


  def print(prefix : String) = {
    val p = prefix + ": "
    println(p + "<<<<<<<<<<<<<<<<")
    println(p + "Subproblems: " + count)
    println(p + goals.mkString(";;;"))
    println(p + ">>>>>>>>>>>>>>>")
  }

  def printActiveProblems() = {
    println("minUnsatCore> CORE: ")
    val core =
      for (c <- 0 until count) yield c

    if (count > 1)
      println("NOTAMAZING>")
    if (count > core.length)
      println("AMAZING> " + count + " => " + core.length)

    println("\tminUnsatCore>" + core.mkString(","))
    core.toList
  }

  //
  // OLD IMPLEMENTATION FOR PAIRS
  //

  // var lastGoals = List() : List[List[List[(Int, Int)]]]
  // var currentSubproblem = -1
  // var currentSubgoal = 0
  // var currentPair = 0

  // def removeGoal(subproblem : Int) = {
  //   lastGoals = goals
  //   if (currentSubproblem != subproblem) {
  //     currentSubgoal = 0
  //     currentSubproblem = subproblem
  //   }

  //   goals = 
  //     (for (p <- 0 until count) yield {
  //       if (p == subproblem) {
  //         (for (subgoal <- 0 until goals(p).length) yield {
  //           var retval = goals(p)(subgoal)
  //           if (subgoal == currentSubgoal && currentPair < goals(p)(subgoal).length) {
  //             retval = (goals(p)(subgoal).take(currentPair)) ++ (goals(p)(subgoal).drop(currentPair+1))
  //           } else if (subgoal == currentSubgoal) {
  //             currentSubgoal += 1
  //             currentPair = 0
  //           }
  //           retval
  //         }).toList
  //       } else {
  //         goals(p)
  //       }
  //     }).toList


  //   if (currentSubgoal == goals(subproblem).length)
  //     true
  //   else
  //     false
  // }

  // def restoreGoal() = {
  //   goals = lastGoals
  //   currentPair += 1
  // }

  var lastGoals = List() : List[List[List[(Int, Int)]]]
  var currentSubproblem = -1

  def removeGoal() = {
    currentSubproblem += 1
    if (currentSubproblem >= goals.length) {
      true
    } else {
      lastGoals = goals
      println("minUnsatCore> goalsBefore " + goals)
      goals = goals.take(currentSubproblem) ++ List(List()) ++ goals.drop(currentSubproblem + 1)
      println("minUnsatCore> goalsAfter " + goals)
      false
    }
  }

  def restoreGoal() = {
    goals = lastGoals
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

  def addDerivedColumn() = {
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
          val argBit = alloc.alloc(1)
          gt.and(argBit, new VecInt(argBits))

          // gtBit <=> C_p[s_i] > C_p[s_j]
          val gtBit = termGtTerm((currentColumn-1, s_i), (currentColumn-1, s_j))

          // vBit <=> args_i = args_j ^ s_i > s_j
          val vBit = alloc.alloc(1)
          gt.and(vBit, argBit, gtBit)

          (vBit, (args_i, s_i), (args_j, s_j))
        }


      for (t <- terms) {
        // --- CASE0: Not a representing term, following a rowless bit ---
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

        val funcBits =
          (for ((vBit, (args_i, s_i), (args_j, s_j)) <- V) yield {
            // C_p[s_i] = t
            val prevEqBit = termEqInt((currentColumn - 1, s_i), t)

            // C_c[t] = C_c[s_j]
            val curEqBit = termEqTerm((currentColumn, t), (currentColumn, s_j))

            val fBit = alloc.alloc(1)
            gt.and(fBit, new VecInt(Array(vBit, prevEqBit, curEqBit)))
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
    Timer.measure("addGoalConstraint") {
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

  def addVConstraint() = {
    // termToIndex
    val tTI = (for (t <- terms) yield (t, terms indexOf t)).toMap

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
        val argBit = alloc.alloc(1)
        gt.and(argBit, new VecInt(argBits))

        // gtBit <=> C_p[s_i] > C_p[s_j]
        val gtBit = termGtTerm((currentColumn, s_i), (currentColumn, s_j))

        // vBit <=> args_i = args_j ^ s_i > s_j
        val vBit = alloc.alloc(1)
        gt.and(vBit, argBit, gtBit)

        vBit
      }

    if (V.isEmpty)
      None
    else
      Some(solver.addClause(new VecInt(V.toArray)))
  }
}

class CCUSolver[TERM, FUNC] {
  val alloc = new Allocator(1)

  val ZEROBIT = alloc.alloc(1)
  val ONEBIT = alloc.alloc(1)

  var tableComplete = false
  var tables = List() : List[Table[FUNC]]
  var problem = 
    new Problem[TERM, FUNC](0, List(), Map(), List(List()), List(Map()), 
      List(), List(), 0, List(), Map())
  var termToInt = Map() : Map[TERM, Int]
  var intToTerm = Map() : Map[Int, TERM]

  // SAT4J stuff
  val asd = (Timer.measure("SAT4Jinit") {
    val solverasd = SolverFactory.newDefault()
    val gtasd = new GateTranslator(solverasd)
    

    // TODO: Make real bound?
    val MAXVAR = 1000000;
    solverasd.newVar (MAXVAR);
    (solverasd, gtasd)
  }) : (ISolver, GateTranslator)
  val (solver, gt) = asd

  //
  //  Disequality check
  //

  // List all disequalities, and see which ones can never be united
  // Only send in pairs that are possible, so domains doesn't have to be passed
  // eq shows POSSIBLE equalities
  def disequalityCheck(eq : Array[Array[Int]],
    functions : List[(FUNC, List[Int], Int)]) = {

    var changed = true
    while (changed) {
      changed = false

      // Functionality & Transitivity
      for ((f_i, args_i, s_i) <- functions;
        (f_j, args_j, s_j) <- functions;
        if (f_i == f_j && s_i != s_j))
      {
        var equal = true
        for (i <- 0 until args_i.length) {
          if (eq(args_i(i) min args_j(i))(args_i(i) max args_j(i)) == 0) {
            equal = false
          }
        }

        // Functionality
        if (equal) {
          if (eq(s_i min s_j)(s_i max s_j) == 0) {
            // println(">" + s_i + " = " + s_j + ", because of " +
            // f_i + "(" + args_i + ") = " + f_j + "(" + args_j + ")")
            eq(s_i)(s_j) = 1
            eq(s_j)(s_i) = 1
            changed = true
          }

          // "Transitivity"
          for (i <- 0 until eq.length) {
            for (j <- 0 until eq.length) {
              if (eq(s_i)(i) != 0 && eq(s_j)(j) != 0 && eq(i)(j) == 0) {
                // println(">" + i + " = " + j + ", because of " + s_i +
                // " = " + i + " and " + s_j + " = " + j)
                eq(i)(j) = 1
                eq(j)(i) = 1
                changed = true
              }
            }
          }
        }
      }

    }
    eq
  }


  //
  // MATH HELPER FUNCTIONS
  //
  
  // Calculating log_2 (b)
  // Used for cacluating number of bits needed
  def binlog(b : Int) : Int = {
    Timer.measure("binlog") {
      var bits = b
      var log = 0
      if ((bits & 0xffff0000) != 0) {
        bits >>>= 16
        log = 16
      }
      
      if (bits >= 256) {
        bits >>>= 8
        log += 8
      }
      if (bits >= 16) {
        bits >>>= 4
        log += 4
      }
      
      if (bits >= 4) {
        bits >>>= 2
        log += 2
      }

      // TODO: Add 1 for luck!
      // Actually only needed for 2, 4, 8, 16, 32 ...
      return log + ( bits >>> 1 ) + 1
    }
  }


  //
  //
  //  PROBLEM PRINTING FUNCTIONS
  //
  //

  def printProblem(terms : List[Int],
    domains : Map[Int, Set[Int]],
    goals : List[List[List[(Int, Int)]]],
    functions : List[List[(FUNC, List[Int], Int)]]) = {
    println("/--PROBLEM--\\")
    for (t <- terms)
      println("| " + t + " = {" +
        (domains.getOrElse(t, Set(t))).mkString(", ") + "}")
    val problemCount = goals.length
    println("| ProblemCount: " + problemCount)
    for (p <- 0 until problemCount) {
      println("| -----------")
      println("| Goals: " + goals(p).mkString(", "))
      println("| Functions: " + functions(p).mkString(", "))
    }
    println("\\----------/")
  }

  def printProblemLazy(terms : List[Int],
    domains : Map[Int, Set[Int]],
    goals : List[List[List[(Int, Int)]]],
    functions : List[List[(FUNC, List[Int], Int)]]) = {
    println("LAZY: /--PROBLEM--\\")
    for (t <- terms)
      println("LAZY: | " + t + " = {" +
        (domains.getOrElse(t, Set(t))).mkString(", ") + "}")
    val problemCount = goals.length
    println("LAZY: | ProblemCount: " + problemCount)
    for (p <- 0 until problemCount) {
      println("LAZY: | -----------")
      println("LAZY: | Goals: " + goals(p).mkString(", "))
      println("LAZY: | Functions: " + functions(p).mkString(", "))
    }
    println("LAZY: \\----------/")
  }

  //
  //
  //  SOLVER
  //
  //



  def createProblem(
    terms : List[TERM],
    domains : Map[TERM, Set[TERM]],
    goals : List[List[List[(TERM, TERM)]]],
    functions : List[List[(FUNC, List[TERM], TERM)]]) : 
      Problem[TERM, FUNC] = {

    // TODO: optimize such that each table has its own bits
    val bits = binlog(terms.length)

    // HACK?
    val problemCount = goals.length

    // Convert to Int representation
    termToInt = Map()
    intToTerm = Map()
    var assigned = 0

    while (assigned < terms.length) {
      for (t <- terms) {
        if (!(termToInt contains t)) {
          var domainAssigned = true
          for (tt <- (domains.getOrElse(t, Set())); if (t != tt)) {
            if (!(termToInt contains tt))
              domainAssigned = false
          }
          if (domainAssigned) {
            termToInt += (t -> assigned)
            intToTerm += (assigned -> t)
            assigned += 1
          }
        }
      }
    }

    // Adjust to new representation

    val newTerms = terms.map(termToInt)

    var newDomains = Map() : Map[Int, Set[Int]]
    for (t <- terms) {
      val oldDomain = domains.getOrElse(t, Set(t))
      newDomains += (termToInt(t) -> oldDomain.map(termToInt))
    }

    val newGoals =
      for (g <- goals)
      yield (for (eqs <- g)
      yield for ((s, t) <- eqs) yield (termToInt(s), termToInt(t)))

    val newFunctions =
      for (funs <- functions)
      yield (for ((f, args, r) <- funs)
      yield (f, args.map(termToInt), termToInt(r)))


    //
    // --- DISEQUALITY CHECK ---
    // Check if goals are even possible to unify
    // If not we can immeadietly return UNSAT
    val arr = Array.ofDim[Int](newTerms.length, newTerms.length)
    
    for (t <- newTerms) {
      val domain = newDomains.getOrElse(t, List(t))
      for (d <- domain) {
        arr(t)(d) = 1
        arr(d)(t) = 1
      }

      for (tt <- newTerms; if t != tt) {
        for (ttt <- newTerms) {
          if ((newDomains.getOrElse(t, Set(t)) contains ttt) && (newDomains.getOrElse(tt, Set(tt)) contains ttt)) {
            arr(t)(tt) = 1
            arr(tt)(t) = 1
          }
        }
      }
    }


    // println("arr: \n" + arr.map(x => x.mkString(" ")).mkString("\n"))

    val diseq = (for (p <- 0 until problemCount)
    yield
    {
      val c = Array.ofDim[Int](newTerms.length, newTerms.length)
      for (t <- newTerms; tt <- newTerms)
        c(t)(tt) = arr(t)(tt)

      val deq = disequalityCheck(c, newFunctions(p))
      deq
    }).toList


    printProblem(newTerms, newDomains, newGoals, newFunctions)

    // for (d <- diseq)
    //   println("diseq: \n" + d.map(x => x.mkString(" ")).mkString("\n"))

    // Create tables


    val ffs =
      (for (p <- 0 until problemCount) yield {
        // Filter terms per table
        def isUsed(term : Int, functions : List[(FUNC, List[Int], Int)],
          goals : List[List[(Int, Int)]]) : Boolean = {
          for ((_, args, s) <- functions) {
            if (s == term)
              return true
            for (a <- args)
              if (a == term)
                return true
          }

          for (g <- goals)
            for ((s, t) <- g)
              if (s == term || t == term)
                return true

          false
        }

        // TODO: Check arguments agains diseq?
        def matchable(funs : List[(FUNC, List[Int], Int)],
          fun : (FUNC, List[Int], Int)) : Boolean = {
          val (f1, args1, s1) = fun
          for ((f2, args2, s2) <- funs) {
            if (f1 == f2 && s1 != s2) {
              var m = true
              for ((a1, a2) <- args1 zip args2)
                if (diseq(p)(a1)(a2) == 0)
                  m = false

              if (m)
                return true
            }
          }
          false
        }

        val ff =
          newFunctions(p).filter(x => (matchable(newFunctions(p), x))).toList
        val ft =
          newTerms.filter(x => isUsed(x, ff, newGoals(p))).toList
        val fd =
          (for ((t, d) <- newDomains) yield {
            (t, d.filter(x => ft contains x))
          }).toMap
        (ff, ft, fd)
      }).toList : List[(List[(FUNC, List[Int], Int)], List[Int], Map[Int, Set[Int]])]

    val filterTerms = for ((_, ft, _) <- ffs) yield ft
    val filterDomains = for ((_, _, fd) <- ffs) yield fd
    val filterFunctions = for ((ff, _, _) <- ffs) yield ff


    val problem =
      new Problem[TERM, FUNC](problemCount, newTerms, newDomains, 
        filterTerms, filterDomains, newGoals, filterFunctions, bits, diseq, Map())

    problem
  }

  def solveaux() 
      : (Option[Array[Int]], Map[Int, List[Int]]) = {
    Timer.measure("Solveaux") {
      println("solveaux")
      // We have p problems, and we are dealing with the simultaneous problem,
      // i.e. every problem must be solvable
      var allGoalPossible = true

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
        println("\tDISEQUALITY CHECK DEEMS PROBLEM IMPOSSIBLE")
        return (None, Map())
      }

      println("diseqed goals: " + diseqedGoals)
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


      val assignments =
        (for (t <- terms) yield {
          (t,
            (if (domains(t).size == 1) {
              termAssIntAux(domains(t).toList(0))
            } else {
              val termStartBit = alloc.alloc(bits)
              val termBits = List.tabulate(bits)(x => x + termStartBit)
              val assBits =
                (for (tt <- domains(t); if tt <= t) yield  {
                  val tmpBit = termEqIntAux(termBits, tt)
                  tmpBit
                }).toArray
              solver.addClause(new VecInt(assBits))
              termBits}).toList)}).toMap

      println(assignments)

      // Enforce idempotent solutions
      for (t <- terms) {
        for (tt <- domains(t); if tt <= t) {
          // Either tt = tt or t != tt
          val iddBit = termEqIntAux(assignments(tt), tt)
          val neqBit = -termEqIntAux(assignments(t), tt)
          solver.addClause(new VecInt(Array(iddBit, neqBit)))
        }
      }
      
      for (p <- 0 until problemCount)
        tables(p).addInitialColumn(assignments)

      for (p <- 0 until problemCount) {
        tables(p).addDerivedColumn()
      }

      while (cont) {
        val goalConstraints =
          for (p <- 0 until problemCount; if (!goals(p).isEmpty)) yield
            tables(p).addGoalConstraint(goals(p))

        Timer.measure("isSat") {
          if (solver.isSatisfiable()) {

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

            model = Option(solver.model)
            // for (p <- 0 until problemCount) {
            //   println("TABLE " + p)
            //   for (t <- tables(p).terms) {
            //     print(t + ">\t")
            //     for (c <- 0 to tables(p).currentColumn) {
            //       val i = bitToInt(tables(p)(c, t))
            //       print("(" + tables(p)(c, t) + " => " + i + ") ")
            //     }
            //     println
            //   }
            // }

            // println(model.mkString(" "))
            cont = false
          } else {
            for (gc <- goalConstraints)
              solver.removeConstr(gc)

            def CCPerTable() : Boolean = {
              // Check table per table
              for (p <- 0 until problemCount) {
                val cc = 
                  tables(p).addCompletionConstraint()

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

              val sat = solver.isSatisfiable()
              for (cc <- ccs)
                solver.removeConstr(cc)

              sat
            }

            def CCV() : Boolean = {
              val ccs =
                for (p <- 0 until problemCount) yield
                  tables(p).addVConstraint() match {
                    case Some(cc) => cc
                    case None => return false
                  }


              val sat = solver.isSatisfiable()
              for (cc <- ccs)
                solver.removeConstr(cc)

              sat
            }


            Timer.measure("completionConstraint_" + tables(0).currentColumn + "_columns") {
              val moreInfo = CCV()

              if (!moreInfo) {
                println("Table completed!")
                for (p <- 0 until problemCount)
                  println("Terms: " + tables(p).terms)
                tableComplete = true
                model = None
                cont = false
              } else {
                for (p <- 0 until problemCount)
                  tables(p).addDerivedColumn()
              }
            }
          }
        }
      }

      // TODO: Change if differents rows
      Timer.measure("Columns_" +
        (for (p <- 0 until problemCount)
        yield tables(p).currentColumn).mkString("[", " ", "]")) { true }

      // println("\tColumns: " +
      //   (for (p <- 0 until problemCount)
      //   yield tables(p).currentColumn).mkString("[", " ", "]"))
      // println("\tVariables: " + solver.realNumberOfVariables())
      (model, assignments)
    }
  }

  // Given a list of domains, goals, functions, see if there is a solution to
  // the simultaneous problem.

  def solve_asserted(
    terms : List[TERM],
    domains : Map[TERM, Set[TERM]],
    goals : List[List[List[(TERM, TERM)]]],
    functions : List[List[(FUNC, List[TERM], TERM)]])
      : Option[Map[TERM, TERM]] = {
    Timer.measure("Solve") {
      println("\n")
      // TODO: Build up terms automatically

      if (terms.isEmpty || goals.isEmpty)
        return None

      for (g <- goals)
        if (g.isEmpty)
          return None

      // HACK?
      val problemCount = goals.length

      // println("diseqedGoals: " + diseqedGoals)

      // Solve and return UNSAT or SAT  + model
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

      problem = createProblem(terms, domains, goals, functions)

      solveaux() match {
        case (Some(model), assignments) => {
          var assMap = Map() : Map[TERM, TERM]
          for (t <- problem.allTerms) {
            val iVal = bitToInt(assignments(t))
            // println(t + " := " + iVal)
            assMap += (intToTerm(t) -> intToTerm(iVal))
          }

          Some(assMap)
        }

        case (None, _) =>  {
          None
        }
      }
    }
  }

  def CC[FUNC, TERM](sets : MSet[Set[TERM]], functions : List[(FUNC, List[TERM], TERM)],
    assignments : List[(TERM, TERM)] = List()) : Set[Set[TERM]] = {
    def rep(t : TERM) : TERM = {
      for (s <- sets)
        if (s contains t)
          return s.minBy(_.toString)
      throw new Exception("No set contains t?")
    }

    def set(t : TERM) : Set[TERM] = {
      for (s <- sets)
        if (s contains t)
          return s
      throw new Exception("No set contains t?")
    }

    def mergeSets(t1 : TERM, t2 : TERM) : Unit = {
      val set1 = set(t1)
      val set2 = set(t2)

      val newset = set1 ++ set2
      sets -= set1
      sets -= set2
      sets += newset
    }

    // First merge assigned terms
    for ((s, t) <- assignments) {
      mergeSets(s, t)
    }

    // Fix-point calculation
    var changed = true
    while (changed) {
      changed = false
      // All pairs of functions, if args_i = args_j, merge s_i with s_j
      for ((f_i, args_i, s_i) <- functions;
        (f_j, args_j, s_j) <- functions;
        if (f_i == f_j && set(s_i) != set(s_j))) {
        var argsEquals = true
        for (i <- 0 until args_i.length) {

          if (set(args_i(i)) != set(args_j(i)))
            argsEquals = false
        }
        if (argsEquals) {
          mergeSets(s_i, s_j)
          changed = true
        }
      }
    }

    sets.toSet
  }

  def CCwithDiseq[FUNC](sets : MSet[Set[Int]], functions : List[(FUNC, List[Int], Int)],
    diseq : Array[Array[Int]]) : Set[Set[Int]] = {
    def rep(t : Int) : Int = {
      for (s <- sets)
        if (s contains t)
          return s.minBy(_.toString)
      throw new Exception("No set contains t?")
    }

    def set(t : Int) : Set[Int] = {
      for (s <- sets)
        if (s contains t)
          return s
      throw new Exception("No set contains t?")
    }

    def mergeSets(t1 : Int, t2 : Int) : Unit = {
      val set1 = set(t1)
      val set2 = set(t2)

      val newset = set1 ++ set2
      sets -= set1
      sets -= set2
      sets += newset
    }

    // First merge no diseq-sets
    for (s <- 0 until diseq.length; t <- 0 until diseq.length; if (s < t); 
      if (diseq(s)(t) != 0))
      mergeSets(s, t)

    // Fix-point calculation
    var changed = true
    while (changed) {
      changed = false
      // All pairs of functions, if args_i = args_j, merge s_i with s_j
      for ((f_i, args_i, s_i) <- functions;
        (f_j, args_j, s_j) <- functions;
        if (f_i == f_j && set(s_i) != set(s_j))) {
        var argsEquals = true
        for (i <- 0 until args_i.length) {

          if (set(args_i(i)) != set(args_j(i)))
            argsEquals = false
        }
        if (argsEquals) {
          mergeSets(s_i, s_j)
          changed = true
        }
      }
    }

    sets.toSet
  }

  def checkSAT(
    terms : List[TERM],
    domains : Map[TERM, Set[TERM]],
    goals : List[List[List[(TERM, TERM)]]],
    functions : List[List[(FUNC, List[TERM], TERM)]],
    solution : Map[TERM, TERM]) : Boolean = {

    val sets = MSet() : MSet[Set[TERM]]
    for (t <- terms)
      sets += Set(t)

    def set(t : TERM) : Set[TERM] = {
      for (s <- sets)
        if (s contains t)
          return s
      throw new Exception("No set contains t?")
    }


    for (p <- 0 until functions.length) {
      // println("\n\nSETS BEFORE:")
      // println(sets.mkString("\n"))
      // println("SOLUTION: " + solution)
      // println("FUNCTIONS: " + functions(p))
      CC(sets, functions(p), solution.toList)
      // println("\n\nSETS AFTER: ")
      // println(sets.mkString("\n"))
      // println(goals(p))
      // Of these subgoals, one must be true
      var anySubGoalTrue = false
      for (subGoal <- goals(p)) {
        var allPairsTrue = true
        for ((s,t) <- subGoal) {
          if (set(s) != set(t)) {
            allPairsTrue = false
          }
        }
        if (allPairsTrue)
          anySubGoalTrue = true
      }

      if (!anySubGoalTrue) {
        return false
      }
    }

    true
  }

  def checkUNSAT(
    terms : List[TERM],
    domains : Map[TERM, Set[TERM]],
    goals : List[List[List[(TERM, TERM)]]],
    functions : List[List[(FUNC, List[TERM], TERM)]]) : Boolean = {
    // Enumerate all solutions and do a check sat
    
    if (domains.isEmpty) {
      !(checkSAT(terms, domains, goals, functions, Map()))
    } else {
      // 1. Convert domain to lists of tuples
      var totalSolutions = 1

      val newDomains =
        (for ((k, v) <- domains) yield {
          var tmp = 0
          val asd = (for (vv <- v) yield {
            tmp += 1
            (k, vv)
          }).toList
          totalSolutions *= tmp
          asd
        }).toList

      var checkedSolutions = 0
      // 2. Form all solutions
      def formSolutions(dom : List[List[(TERM, TERM)]], sol : Map[TERM, TERM])
          : Option[Map[TERM, TERM]] = {
        if (dom.isEmpty) {
          checkedSolutions += 1
          if (checkedSolutions % 100000 == 0)
            println("Checked " + checkedSolutions + "/" + totalSolutions)
          if (checkSAT(terms, domains, goals, functions, sol.toMap)) {
            Some(sol)
          } else {
            None
          }
        } else {
          for ((k, v) <- dom.head) {
            val isSol = formSolutions(dom.tail, sol + (k -> v))
            if (isSol.isDefined)
              return isSol
          }
          None
        }
      }

      val result = formSolutions(newDomains, Map())
      if (result.isDefined) {
        println("THERE IS SOLUTION: " + result.get)
        false
      } else {
        true
      }
    }
  }

  def solve(
    terms : List[TERM],
    domains : Map[TERM, Set[TERM]],
    goals : List[List[List[(TERM, TERM)]]],
    functions : List[List[(FUNC, List[TERM], TERM)]])
      : Option[Map[TERM, TERM]] = {



    solver.reset()
    tableComplete = false

    solve_lazy(terms, domains, goals, functions) match {
      case Some(sol) =>
        return Some(sol)
        print("Verifying SAT...")
        if (!checkSAT(terms, domains, goals, functions, sol)) {
          println("FALSE SAT!")
          throw new Exception("FalseSATException")
        } else {
          println("OK!")
          Some(sol)
        }
      case None =>
        // println("minUnsatCore> Calculating minimum unsat core")
        // minUnsatCore()
        // problem.print()
        return None

        print("Verifying UNSAT...")
        if (!checkUNSAT(terms, domains, goals, functions)) {
          println("FALSE UNSAT!")
          throw new Exception("FalseUNSATException")
        } else {
          println("OK!")
          None
        }
    }
  }

  def solveAgain() : Boolean = {
    if (problem.goals.flatten.flatten.isEmpty)
      return true

    var retval = false : Boolean

    if (tableComplete) {
      val goals = problem.goals

      val goalConstraints =
        for (p <- 0 until problem.count; if (!goals(p).flatten.isEmpty)) yield {
          println("TABLE " + p)
          println("\t" + tables(p).terms)
          println(goals(p))
          tables(p).addGoalConstraint(goals(p))
        }
      retval =  solver.isSatisfiable()

      for (gc <- goalConstraints)
        solver.removeConstr(gc)
    } else {
      solveaux() match {
        case (Some(_), _) => retval = true
        case (None, _) => retval = false
      }
    }

    retval
  }



  // PRE: Call after solve returns UNSAT
  def minUnsatCore() : List[Int] = {
    println("minUnsatCore")
    // Find minimum subset of goals that still yields unsat
    // So in this case we have a unsat, so we greedily remove goals until 
    // it goes SAT then we return last one before


    println("minUnsatCore> BEGIN")
    // println("minUnsatCore> Tables: " + tables.length)
    // Try removing the first goal from the the first problem, etc.

    problem.print("minUnsatCore")

    for (p <- 0 until problem.count) {
      var end = false
      while (!end) {
        // println("minUnsatCore> removeGoal(" + p + ")")
        end = problem.removeGoal()
        // Problem was sat with p removed => restore
        if (solveAgain()) {
          println("minUnsatCore> problem restored")
          problem.restoreGoal()
        } else
          println("minUnsatCore> PROBLEM REMOVED!")
      }
    }

    
    val unsatCore = problem.printActiveProblems()
    problem.print("minUnsatCore")


    println("minUnsatCore>END")
    unsatCore
  }
}

