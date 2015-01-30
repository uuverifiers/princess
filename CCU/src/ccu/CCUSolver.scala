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

object Result extends Enumeration {
  type Result = Value
  val SAT, UNSAT = Value
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
  val termMap : Map[TERM, Int],
  val intMap : Map[Int, TERM])
{ 

  // SubGoal removal variables

  def print(prefix : String) = {
    val p = prefix + ": "

    for (t <- allTerms)
      println("| " + t + " = {" +
        (allDomains.getOrElse(t, Set(t))).mkString(", ") + "}")
    println("| Count: " + count)
    for (p <- 0 until count) {
      println("| -----------")
      println("| Goals: " + goals(p).mkString(", "))
      println("| Functions: " + functions(p).mkString(", "))
    }
    println("\\----------/")
  }

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

abstract class CCUSolver[TERM, FUNC] {

  def solve() : Result.Result
  def minUnsatCore() : List[Int]

  val util = new Util[TERM, FUNC]
  val alloc = new Allocator(1)
  val ZEROBIT = alloc.alloc(1)
  val ONEBIT = alloc.alloc(1)

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

  var problem = new Problem[TERM, FUNC](0, List(), Map(), List(List()), 
    List(Map()), List(), List(), 0, List(), Map(), Map())

  var termToInt = Map() : Map[TERM, Int]
  var intToTerm = Map() : Map[Int, TERM]

  // Verifies that an assignment with functions solves goal
  // This is exact, i.e. if it returns true then assignment
  // IS a solution, and if it returns false it is NOT a
  // solution

  def reset() = {
    solver.reset()
    alloc.next = 1
    problem = new Problem[TERM, FUNC](0, List(), Map(), List(List()), 
    List(Map()), List(), List(), 0, List(), Map(), Map())
  }

  // TODO: just check the relevant terms (i.e. problem.terms(p))
  def verifySolution[TERM, FUNC](
    terms : List[TERM],
    assignment : Map[TERM,TERM],
    functions : List[(FUNC, List[TERM], TERM)],
    goals : List[List[(TERM, TERM)]])
      : Boolean = {

    val sets = MSet() : MSet[Set[TERM]]
    for (t <- terms)
      sets += Set(t)

    val newSets = util.CC[FUNC, TERM](sets, functions, assignment.toList)

    def set(t : TERM) : Set[TERM] = {
      for (s <- newSets)
        if (s contains t)
          return s
      throw new Exception("No set contains t?")
    }

    var satisfiable = false

    for (subGoal <- goals) {
      var subGoalSat = true

      var allPairsTrue = true
      for ((s,t) <- subGoal) {
        if (set(s) != set(t)) {
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


  def bitToInt(bits : List[Int]) : Int = {
    var curMul = 1
    var curVal = 0
    for (b <- bits) {
      if (solver.model contains b)
        curVal += curMul
      curMul *= 2
    }
    curVal
  }

  def termAssIntAux(i : Int) = {
    var curVal = i

    for (b <- 0 until problem.bits) yield {
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

  def termEqTermAux(term1Bits : List[Int], term2Bits : List[Int]) : Int = {
    Timer.measure("termEqTerm") {
      val maxBits = term1Bits.length max term2Bits.length

      val term1BitsPadded = term1Bits.padTo(maxBits, ZEROBIT)
      val term2BitsPadded = term2Bits.padTo(maxBits, ZEROBIT)

      // TODO: Could be optimised (by not doing padding...)
      val eqBits =
        (for ((t1b, t2b) <- term1BitsPadded zip term2BitsPadded) yield {
          // TODO: reply by match?
          if (t1b == ZEROBIT && t2b == ZEROBIT || t1b == ONEBIT && t2b == ONEBIT) {
            ONEBIT
          } else if (t1b == ZEROBIT && t2b == ONEBIT || t1b == ONEBIT && t2b == ZEROBIT) {
            return ZEROBIT
          } else {
            var tmpBit = alloc.alloc(1)
            gt.iff(tmpBit, new VecInt(Array(t1b, t2b)))
            tmpBit
          }
        }).toArray

      var eqBit = alloc.alloc(1)
      gt.and(eqBit, new VecInt(eqBits))
      eqBit
    }
  }

  def createAssignments(terms : List[Int]) : Map[Int, List[Int]] = {
    // Connects each term with its list of bits
    // (e.g. assignment(a) = List(3,4,5))
    val assignments =
      (for (t <- terms) yield {
        (t,
          (if (problem.allDomains(t).size == 1) {
            termAssIntAux(problem.allDomains(t).toList(0))
          } else {
            val termStartBit = alloc.alloc(problem.bits)
            val termBits = List.tabulate(problem.bits)(x => x + termStartBit)
            val assBits =
              (for (tt <- problem.allDomains(t); if tt <= t) yield  {
                termEqIntAux(termBits, tt)
              }).toArray
            solver.addClause(new VecInt(assBits))
            termBits}).toList)}).toMap

    // Enforce idempotency
    for (t <- terms) {
      for (tt <- problem.allDomains(t); if tt <= t) {
        // Either tt = tt or t != tt
        val iddBit = termEqIntAux(assignments(tt), tt)
        val neqBit = -termEqIntAux(assignments(t), tt)
        solver.addClause(new VecInt(Array(iddBit, neqBit)))
      }
    }
    assignments
  }

  def createProblem(
    domains : Map[TERM, Set[TERM]],
    goals : List[List[List[(TERM, TERM)]]],
    functions : List[List[(FUNC, List[TERM], TERM)]]) : Boolean = {

    // TODO: Create terms automatically
    val termSet = MSet() : MSet[TERM]
    for ((_, d) <- domains) 
      for (t <- d)
        termSet += t
    for ((s,t) <- goals.flatten.flatten) {
      termSet += s
      termSet += t
    }
    for ((_, args, r) <- functions.flatten) {
      for (t <- args)
        termSet += t
      termSet += r
    }
    
    val terms = termSet.toList

    // TODO: optimize such that each table has its own bits
    val bits = util.binlog(terms.length)

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

    val diseq = (for (p <- 0 until problemCount)
    yield
    {
      val c = Array.ofDim[Int](newTerms.length, newTerms.length)
      for (t <- newTerms; tt <- newTerms)
        c(t)(tt) = arr(t)(tt)

      val deq = util.disequalityCheck(c, newFunctions(p))
      deq
    }).toList

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


    problem =
      new Problem[TERM, FUNC](problemCount, newTerms, newDomains, 
        filterTerms, filterDomains, newGoals, filterFunctions, bits, diseq, 
        termToInt, intToTerm)

    
    false
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


    for (p <- 0 until functions.length)
      if (!verifySolution[TERM, FUNC](terms, solution, functions(p), goals(p)))
        return false

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

          if (checkSAT(terms, domains, goals, functions, Map())) {
          // if (verifySolution[TERM, FUNC](terms, sol.toMap, functions, goals)) {
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
}

