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

class Allocator {
  // Leave room for ONEBIT (1) and ZEROBIT (2)
  var next = 3

  def reset = { 
    next = 3 
  }

  def alloc(count : Int) = {
    val ret = next
    next = next + count
    ret
  }
}

object Result extends Enumeration {
  type Result = Value
  val SAT, UNSAT, UNKNOWN = Value
}

class Problem(
  val terms : Seq[Int],
  val domains : Map[Int, Set[Int]],
  val funEqs : Seq[(Int, Seq[Int], Int)],
  val goal : Seq[Seq[(Int, Int)]],
  val DQ : Disequalities)
{
  var active = true

  def print = {
    println("| funEqs: " + funEqs)
    println("| goal: " + goal)
  }
}

  // val diseq : Seq[Array[Array[Int]]],
  // val diseqArray : Seq[Array[Int]],

class SimProblem[TERM, FUNC](
  val terms : Seq[Int],
  val domains : Map[Int, Set[Int]],
  val bits : Int,
  val baseDI : Seq[Array[Array[Int]]],
  val termMap : Map[TERM, Int],
  val intMap : Map[Int, TERM],
  val order : Seq[Int],
  val problems : Seq[Problem]) {

  val count = problems.length

  // def newDiseq(i : Int, j : Int) = {
  //   val retVal = diseqArray(i * terms.length + j)
  //   if (retVal != diseq(i)(j))
  //     throw new Exception("DISEQ ERROR")
  //   retVal
  // }

  var result = None : Option[ccu.Result.Result]
  var intAss = Map() : Map[Int, Int]

  def print = {
    println("//-------------")
    for (t <- terms)
      println("| " + t + " = {" +
        (domains.getOrElse(t, Set(t))).mkString(", ") + "}")
    println("| Count: " + count)
    for (p <- 0 until count) {
      println("+--------")
      problems(p).print
    }
    println("\\\\-------------")
  }

  def deactivateProblem(p : Int) = {
    problems(p).active = false
  }

  def activateProblem(p : Int) = {
    problems(p).active = true
  }
}

class CCUInstance[TERM, FUNC](
  id : Int, 
  solver : CCUSolver[TERM, FUNC]) {

  def confirmActive = {
    if (solver.curId != id)
      throw new Exception("New instance has been created by solver")
  }

  def solve = {
    confirmActive
    val result = 
      try {
        solver.solveAsserted
      } catch {
        case to : org.sat4j.specs.TimeoutException => {
          ccu.Result.UNKNOWN
        }
      }

    result
  }

  def solveAsserted = {
    confirmActive
    solver.solveAsserted
  }

  def notUnifiable(problem : Int, s : TERM, t : TERM) : Boolean = {
    confirmActive
    (for (i <- solver.problem.termMap get s;
          j <- solver.problem.termMap get t)
     yield (!solver.problem.problems(problem).DQ(i, j))) getOrElse (s != t)
  }

  def unsatCore(timeout : Int) = {
    confirmActive
    val core =
      try {
        solver.unsatCore(timeout)
      } catch {
        case to : org.sat4j.specs.TimeoutException => {
          (0 until solver.problem.count)
        }
      }
    core
  }

}

abstract class CCUSolver[TERM, FUNC](val timeoutChecker : () => Unit,
                                     val maxSolverRuntime : Long) {

  def checkPreviousSolution = {
    var ss = true
    if (model.isDefined) {
      val oldModel = model.get
      val newTerms = problem.terms.map(problem.intMap)
      val newModel =
        (for (t <- newTerms) yield {
          val newKey = problem.termMap(t)
          val oldAss = oldModel.getOrElse(t, t)
          val newAss = problem.termMap.getOrElse(oldAss, newKey)
          (newKey, newAss)
        }).toMap



      // println("Checking previous model...")
      for (p <- problem.problems) {
        if (!verifySolution[Int, Int](problem.terms, newModel, p.funEqs, p.goal)) {
          // println("\tNO")
          ss = false
        }
      }

      // Update model
      if (ss) {
        model = Some((for ((k, v) <- newModel) yield {
          (problem.intMap(k), problem.intMap(v))
        }).toMap)
      }

    } else {
      ss = false
    }

    ss
  }
  def solveaux() : Result.Result

  def checkAndSolve() : Result.Result = {
    if (checkPreviousSolution) {
      ccu.Result.SAT
    } else {
      solveaux()
    }
  }

  def solve() = checkAndSolve()

  var model = None : Option[Map[TERM, TERM]]
  def getModel() = model.get
  def unsatCoreAux(timeout : Int) : Seq[Int]
  def unsatCore(timeout : Int) = {
    val core = 
      unsatCoreAux(timeout)
    val retval =
      (for (p <- core) yield (problem.order(p)))

    val m = problem.termMap

    retval
  }

  var curId = 0

  def solveAsserted() = {

    checkAndSolve() match {
      case ccu.Result.SAT => {
        val model = getModel()
        if (!checkSAT(
          origTerms,
          origDomains,
          origGoals,
          origFunctions,
          model)) {
          problem.print
          println("Model: " + model)
          throw new Exception("False SAT")
        }
        // println("SAT ASSERTED")
        ccu.Result.SAT
      }
      case ccu.Result.UNSAT => {
        // if (!checkUNSAT(
        //   origTerms,
        //   origDomains,
        //   origGoals,
        //   origFunctions)) {
        //   throw new Exception("False UNSAT")
        // }
        // println("UNSAT NOT ASSERTED")
        ccu.Result.UNSAT
      }
    }
  }


  // def disequalities(p : Int) : Seq[(TERM, TERM)] = {
  //   (for (i <- 0 until problem.terms.length; 
  //     j <- 0 until problem.terms.length;
  //     if i < j; if (problem.baseDI(p)(i)(j) == 0)) 
  //   yield (problem.intMap(i), problem.intMap(j)))
  // }

  val util = new Util[TERM, FUNC] (timeoutChecker)
  val alloc = new Allocator
  val ZEROBIT = 1
  val ONEBIT = 2

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
  solver.setTimeoutMs(maxSolverRuntime)

  var problem = new SimProblem[TERM, FUNC](List(), Map(), 0, List(),
    Map(), Map(), List(), List())

  var termToInt = Map() : Map[TERM, Int]
  var intToTerm = Map() : Map[Int, TERM]

  // Verifies that an assignment with functions solves goal
  // This is exact, i.e. if it returns true then assignment
  // IS a solution, and if it returns false it is NOT a
  // solution

  def reset = {
    solver.reset()
    alloc.reset
    solver.setTimeoutMs(maxSolverRuntime)
    solver.addClause(new VecInt(Array(-ZEROBIT)))
    solver.addClause(new VecInt(Array(ONEBIT)))
  }

  def modelToAss(assignments : Map[Int, Seq[Int]], model : Array[Int]) = {

    // Convert the model to a more convenient format
    var termAss = Map() : Map[TERM, TERM]
    var intAss = Map() : Map[Int, Int]

    // If bit B is true, bitArray(bitMap(B)) should be true
    var bitMap = Map() : Map[Int, List[Int]]

    // Term T can find its bits in resultMap(T)
    var resultMap = Map() : Map[Int, Seq[Int]]

    // Prune all bits that are not with var ass and put in bitArray
    var bitArray = Array.ofDim[Boolean](problem.terms.length * problem.bits)

    // Current position in bitArray
    var curPos = 0

    for ((term, bits) <- assignments) {
      val newResult =
        (for (i <- 0 until bits.length) yield {
          val newList = curPos :: (bitMap.getOrElse(bits(i), List()))
          bitMap += (bits(i) -> newList)
          curPos += 1
          (curPos - 1)
        })
      resultMap += term -> newResult
    }

    for (i <- solver.model) {
      val newVal = i >= 0
      for (b <- bitMap.getOrElse(Math.abs(i), List()))
        bitArray(b) = newVal
    }

    def bitToInt2(bits : Seq[Int]) = {
      var curMul = 1
      var curVal = 0
      for (b <- bits) {
        if (bitArray(b))
          curVal += curMul
        curMul *= 2
      }
      curVal
    }

    for (t <- problem.terms) {
      val iVal = bitToInt2(resultMap(t))
      termAss += (problem.intMap(t) -> problem.intMap(iVal))
      intAss += (t -> iVal)
    }
    (termAss, intAss)
  }

  // TODO: just check the relevant terms (i.e. problem.terms(p))
  def verifySolution[TERM, FUNC](
    terms : Seq[TERM],
    assignment : Map[TERM,TERM],
    functions : Seq[(FUNC, Seq[TERM], TERM)],
    goals : Seq[Seq[(TERM, TERM)]])
      : Boolean = {

    Timer.measure("verifySolution") {
      val uf = util.CCunionFind[FUNC, TERM](terms, functions, assignment.toList)

      var satisfiable = false

      for (subGoal <- goals) {
        var subGoalSat = true

        var allPairsTrue = true
        for ((s,t) <- subGoal) {
          if (uf(s) != uf(t)) {
            allPairsTrue = false
          }

          if (!allPairsTrue)
            subGoalSat = false
        }
        if (subGoalSat) {
          satisfiable = true
        }
      }
      satisfiable
    }
  }


  def bitToInt(bits : Seq[Int]) : Int = {
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

  def termEqIntAux(bitList : Seq[Int], i : Int) : Int = {
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

  def termEqTermAux(term1Bits : Seq[Int], term2Bits : Seq[Int]) : Int = {
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

  def createAssignments(terms : Seq[Int]) : Map[Int, Seq[Int]] = {
    // Connects each term with its list of bits
    // (e.g. assignment(a) = List(3,4,5))
    var assignments = Map() : Map[Int, Seq[Int]]
    Timer.measure("create.ASSIGNMENTS") {
      assignments =
        (for (t <- terms) yield {
          (t,
            (if (problem.domains(t).size == 1) {
              termAssIntAux(problem.domains(t).toList(0))
            } else {
              val termStartBit = alloc.alloc(problem.bits)
              val termBits = List.tabulate(problem.bits)(x => x + termStartBit)
              val assBits =
                (for (tt <- problem.domains(t); if tt <= t) yield  {
                  termEqIntAux(termBits, tt)
                }).toArray
              solver.addClause(new VecInt(assBits))
              termBits}))}).toMap
    }

    Timer.measure("create.IDEMPOTENCY") {
      // Enforce idempotency
      for (t <- terms) {
        for (tt <- problem.domains(t); if tt <= t) {
          // Either tt = tt or t != tt
          val iddBit = termEqIntAux(assignments(tt), tt)
          val neqBit = -termEqIntAux(assignments(t), tt)
          solver.addClause(new VecInt(Array(iddBit, neqBit)))
        }
      }
    }
    assignments
  }

  // HACK: Keeping original problem
  var origTerms = List() : Seq[TERM]
  var origDomains = Map() : Map[TERM, Set[TERM]]
  var origFunctions = List() : Seq[Seq[(FUNC, Seq[TERM], TERM)]]
  var origGoals = List() : Seq[Seq[Seq[(TERM, TERM)]]]

  def reorderProblems(goals : Seq[Seq[Seq[(Int, Int)]]]) : Seq[Int] = {
    val count = goals.length
    val order  =
      (for (i <- 0 until count) yield
        (i, goals(i).length)).sortBy(_._2).map(_._1)

    order
  }

  def createProblem(
    domains : Map[TERM, Set[TERM]],
    goals : Seq[Seq[Seq[(TERM, TERM)]]],
    functions : Seq[Seq[(FUNC, Seq[TERM], TERM)]]) : CCUInstance[TERM, FUNC] = {
    Timer.measure("createProblem") {
      curId += 1

      // println("CREATE PROBLEM 0")

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
      // println("CREATE PROBLEM 1")

      
      val terms = termSet.toList
      origTerms = terms
      origDomains = domains
      origGoals = goals
      origFunctions = functions

      // TODO: optimize such that each table has its own bits
      val bits = util.binlog(terms.length)

      // HACK?
      val problemCount = goals.length
      // println("CREATE PROBLEM 2")


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
      // println("CREATE PROBLEM 3")


      var funMap = Map() : Map[FUNC, Int]
      assigned = 0
      for ((f, _, _) <- functions.flatten) {
        if (!(funMap contains f)) {
          funMap += (f -> assigned)
          assigned += 1
        }
      }

      // println("CREATE PROBLEM 4")


      // Adjust to new representation

      val newTerms = terms.map(termToInt)

      var newDomains = Map() : Map[Int, Set[Int]]
      for (t <- terms) {
        val oldDomain = domains.getOrElse(t, Set(t))
        newDomains += (termToInt(t) -> oldDomain.map(termToInt))
      }
      // println("CREATE PROBLEM 5")


      val newGoals =
        for (g <- goals)
        yield (for (eqs <- g)
        yield for ((s, t) <- eqs) yield (termToInt(s), termToInt(t)))
      // println("CREATE PROBLEM 6")


      val newFunctions =
        for (funs <- functions)
        yield (for ((f, args, r) <- funs)
        yield (funMap(f), args.map(termToInt), termToInt(r)))

      // println("CREATE PROBLEM 7")


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
          val ttDomain = newDomains.getOrElse(tt, Set(tt))
          if (domain exists ttDomain) {
            arr(t)(tt) = 1
            arr(tt)(t) = 1
          }
        }
      }

      // println("CREATE PROBLEM 8")

      var DQ = List() : Seq[Disequalities]

      Timer.measure("createProblem.DQ") {
        DQ = (for (p <- 0 until problemCount)
        yield {
          // TODO: Length of disequalities
          val tmpDQ = (Timer.measure("createProblem.DQ.new") {
            new Disequalities(newTerms.length, newFunctions(p).toArray, timeoutChecker)
          })
          // val c = Array.ofDim[Int](newTerms.length, newTerms.length)
          for (t <- newTerms; tt <- newTerms)
            if (arr(t)(tt) == 1) {
              Timer.measure("createProblem.DQ.cascadeRemove") {
                tmpDQ.cascadeRemoveDQ(t,tt)
              }
            }
          // c(t)(tt) = arr(t)(tt)

          // val deq = util.disequalityCheck(c, newFunctions(p))
          // deq
          tmpDQ
        })
      }
      // println("CREATE PROBLEM 9")


      val baseDI = (for (p <- 0 until problemCount)
      yield {
        val c = Array.ofDim[Int](newTerms.length, newTerms.length)
        for (t <- newTerms; tt <- newTerms)
          c(t)(tt) = arr(t)(tt)

        arr
        // val deq = util.disequalityCheck(c, newFunctions(p))
        // deq-
      })
      // println("CREATE PROBLEM 10")


      val ffs =
        (for (p <- 0 until problemCount) yield {
          // Filter terms per table
          def isUsed(term : Int, functions : Seq[(Int, Seq[Int], Int)],
            goals : Seq[Seq[(Int, Int)]]) : Boolean = {
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

          // println("CREATE PROBLEM 11")



          def matchable(funs : Seq[(Int, Seq[Int], Int)],
            fun : (Int, Seq[Int], Int)) : Boolean = {
            val (f1, args1, s1) = fun
            for ((f2, args2, s2) <- funs) {
              if (f1 == f2 && s1 != s2) {
                var m = true
                for ((a1, a2) <- args1 zip args2)
                  if (!DQ(p)(a1, a2))
                    m = false

                if (m)
                  return true
              }
            }

            false
          }

          val ff =
            newFunctions(p).filter(x => (matchable(newFunctions(p), x)))

          // println("CREATE PROBLEM 12")


          val tmpFt = ListBuffer() : ListBuffer[Int]
          for (t <- (newTerms.filter(x => isUsed(x, ff, newGoals(p)))))
            tmpFt += t

          // We have to add all terms that are in the domains of ft
          var ftChanged = true
          while (ftChanged) {
            ftChanged = false
            for (t <- tmpFt) {
              for (tt <- newDomains(t)) {
                if (!(tmpFt contains tt)) {
                  tmpFt += tt
                  ftChanged = true
                }
              }
            }
          }

          val ft = tmpFt

          // val ft = newTerms
          // println("CREATE PROBLEM 13")


          val fd =
            (for ((t, d) <- newDomains) yield {
              (t, d.filter(x => ft contains x))
            }).toMap
          // val fd = newDomains
          (ff, ft, fd)
        }) : Seq[(Seq[(Int, Seq[Int], Int)], Seq[Int], Map[Int, Set[Int]])]

      val filterTerms = for ((_, ft, _) <- ffs) yield ft
      val filterDomains = for ((_, _, fd) <- ffs) yield fd
      val filterFunctions = for ((ff, _, _) <- ffs) yield ff
      // println("CREATE PROBLEM 14")



      val order = reorderProblems(newGoals)
      // val order  = 
      //   (for (i <- 0 until problemCount) yield 
      //     (i, newGoals(i).length)).sortBy(_._2).map(_._1)

      // TODO: FIX!
      // println("CREATE PROBLEM 15")


      val reorderTerms = (for (i <- order) yield filterTerms(i))
      val reorderDomains = (for (i <- order) yield filterDomains(i))
      val reorderGoals = (for (i <- order) yield newGoals(i))
      val reorderFunctions = (for (i <- order) yield filterFunctions(i))
      val reorderDQ = (for (i <- order) yield DQ(i))
      val reorderBaseDI = (for (i <- order) yield baseDI(i))

      val problems = 
        for (i <- 0 until problemCount) yield
          new Problem(reorderTerms(i), reorderDomains(i), 
            reorderFunctions(i), reorderGoals(i), reorderDQ(i))
      // println("CREATE PROBLEM 16")


      // val newDiseq = 
      //   for (d <- reorderDiseq) yield {
      //     val newD = Array.ofDim[Int](d.length * d.length)
      //     for (i <- 0 until d.length; j <- 0 until d.length) {
      //       newD(i * d.length + j) = d(i)(j)
      //     }
      //     newD
      //   }

      problem = 
        new SimProblem[TERM,FUNC](
          newTerms,
          newDomains,
          bits,
          // reorderDiseq,
          // newDiseq,
          reorderBaseDI,
          termToInt,
          intToTerm,
          order,
          problems)

      false
    }


    new CCUInstance(curId, this)
  }


  def checkSAT(
    terms : Seq[TERM],
    domains : Map[TERM, Set[TERM]],
    goals : Seq[Seq[Seq[(TERM, TERM)]]],
    functions : Seq[Seq[(FUNC, Seq[TERM], TERM)]],
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


    for (p <- 0 until goals.length)
      if (!verifySolution[TERM, FUNC](terms, solution, functions(p), goals(p)))
        return false

    true
  }

  def checkUNSAT(
    terms : Seq[TERM],
    domains : Map[TERM, Set[TERM]],
    goals : Seq[Seq[Seq[(TERM, TERM)]]],
    functions : Seq[Seq[(FUNC, Seq[TERM], TERM)]]) : Boolean = {
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
        })

      var checkedSolutions = 0
      // 2. Form all solutions
      def formSolutions(dom : Seq[Seq[(TERM, TERM)]], sol : Map[TERM, TERM])
          : Option[Map[TERM, TERM]] = {
        if (dom.isEmpty) {
          checkedSolutions += 1

          if (checkedSolutions % 100000 == 0)
            println("Checked " + checkedSolutions + "/" + totalSolutions)

          if (checkSAT(terms, domains, goals, functions, sol)) {
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

      val result = formSolutions(newDomains.toList, Map())
      if (result.isDefined) {
        val sol = result.get
        println("THERE IS SOLUTION: ")
        for ((k,v) <- sol)
          println("\t" + termToInt(k) + " := " + termToInt(v))
        false
      } else {
        true
      }
    }
  }
}

