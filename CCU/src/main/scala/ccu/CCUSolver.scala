package ccu;

import org.sat4j.core._
import org.sat4j.specs._
import org.sat4j.minisat._
import org.sat4j.tools._

import java.io.FileInputStream
import java.io.ObjectInputStream
import java.io.File

import argonaut._, Argonaut._
import scalaz._, Scalaz._


import Timer._

import scala.collection.mutable.{Map => MMap}
import scala.collection.mutable.{Set => MSet}
import scala.collection.mutable.ListBuffer


//
//  Allocates bits for the solver
//
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


//
//  Three different result types
//  UKNOWN generally indicates an error
//
object Result extends Enumeration {
  type Result = Value
  val SAT, UNSAT, UNKNOWN = Value
}




class Stats { 
  val stats = ListBuffer() : ListBuffer[String]

  def addEntry(s : String) = {
    stats += s
  }

  def clear = stats.clear

  override def toString = {
    stats.mkString("\n")
  }
}

// A superclass for every BREU-solver
abstract class CCUSolver(val timeoutChecker : () => Unit,
                         val maxSolverRuntime : Long) {
  var debug = false
  val S = new Stats

  // var prob = None : Option[CCUSimProblem]
  // def problem = 
  //   if (!prob.isDefined)
  //     throw new Exception("Trying to solve undefined problem!")
  //   else
  //     prob.get

  // Solving
  def statistics = S.toString

  def solve(problem : CCUSimProblem, asserted : Boolean) = {
    val result =
      if (asserted)
        solveAsserted(problem)
      else
        solveaux(problem)

    // println(statistics)

    result match {
      case (ccu.Result.SAT, Some(model)) => {
        // if (!checkSAT(
        //  pp origTerms,
        //   origDomains,
        //   origGoals,
        //   origFunctions,
        //   model)) {
        //   problem.print
        //   println("Model: " + model)
        //   throw new Exception("False SAT")
        // }
        // println("SAT ASSERTED")
        ccu.Result.SAT
      }
      case (ccu.Result.UNSAT, _) => {
        // if (!checkUNSAT(
        //   origTerms,
        //   origDomains,
        //   origGoals,
        //   origFunctions)) {
        //   throw new Exception("False UNSAT")
        // }
        // println("UNSAT ASSERTED")
        ccu.Result.UNSAT
      }
      case _ => throw new Exception("Strange result from solve!")
    }
  }

  // The actual solvefunction
  protected def solveaux(problem : CCUSimProblem) : (Result.Result, Option[Map[Int, Int]])

  // Can we reuse a previous solution?
  def checkAndSolve(problem : CCUSimProblem) = {
    // if (checkPreviousSolution) {
    //   ccu.Result.SAT
    // } else {
      solveaux(problem)
    // }
  }

  def unsatCoreAux(problem : CCUSimProblem, timeout : Int) : Seq[Int]

  // We need to reorder the core
  def unsatCore(problem : CCUSimProblem, timeout : Int) = {
    val core = 
      unsatCoreAux(problem, timeout)

    val retval =
      (for (p <- core) yield (problem.order(p)))

    retval
  }

  var curId = 0

  def solveAsserted(problem : CCUSimProblem) = {
    solveaux(problem)
    // if (!debug && problem.size > 2) {
    //   problem.print
    //   problem.output
    //   util.solveFile("test.txt")
    //   println(10/0)
    // }

    // checkAndSolve(problem) match {
    //   case (ccu.Result.SAT, Some(model)) => {
    //     // if (!checkSAT(
    //     //   origTerms,
    //     //   origDomains,
    //     //   origGoals,
    //     //   origFunctions,
    //     //   model)) {
    //     //   problem.print
    //     //   println("Model: " + model)
    //     //   throw new Exception("False SAT")
    //     // }
    //     // println("SAT ASSERTED")
    //     ccu.Result.SAT
    //   }
    //   case (ccu.Result.UNSAT, _) => {
    //     // if (!checkUNSAT(
    //     //   origTerms,
    //     //   origDomains,
    //     //   origGoals,
    //     //   origFunctions)) {
    //     //   throw new Exception("False UNSAT")
    //     // }
    //     // println("UNSAT ASSERTED")
    //     ccu.Result.UNSAT
    //   }
    //   case _ => throw new Exception("Unexpected Results!")
    // }
  }

  // def disequalities(p : Int) : Seq[(Term, Term)] = {
  //   (for (i <- 0 until problem.terms.length; 
  //     j <- 0 until problem.terms.length;
  //     if i < j; if (problem.baseDI(p)(i)(j) == 0)) 
  //   yield (problem.intMap(i), problem.intMap(j)))
  // }


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
    S.clear
  }


  def assignmentsToSolution[Term](assignments : Map[Int, Seq[Int]]) = {
    val model = solver.model

    // Convert the model to a more convenient format
    var intAss = Map() : Map[Int, Int]

    // If bit B is true, bitArray(bitMap(B)) should be true
    var bitMap = Map() : Map[Int, List[Int]]

    // Term T can find its bits in resultMap(T)
    var resultMap = Map() : Map[Int, Seq[Int]]

    // Prune all bits that are not with var ass and put in bitArray
    // (assuming all terms are represented by the same number of bits)
    var bitArray = 
      Array.ofDim[Boolean](assignments.size * assignments.head._2.size)

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

    for (t <- assignments.keys) {
      val iVal = bitToInt2(resultMap(t))
      intAss += (t -> iVal)
    }
    intAss
  }

  def verifySolution(
    terms : Seq[Int],
    assignment : Map[Int,Int],
    functions : Seq[CCUEq],
    goal : CCUGoal)
      : Boolean = {

    val uf = util.CCunionFind(terms, functions, assignment.toList)

    var satisfiable = false

    for (subGoal <- goal.subGoals) {
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

  def termAssIntAux(i : Int, bits : Int) = {
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

  def termEqIntAux(bitList : Seq[Int], i : Int) : Int = {
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

  def termEqTermAux(term1Bits : Seq[Int], term2Bits : Seq[Int]) : Int = {
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

  def createAssignments(problem : CCUSimProblem) : Map[Int, Seq[Int]] = {
    // Connects each term with its list of bits
    // (e.g. assignment(a) = List(3,4,5))
    val terms = problem.terms 

    var assignments = Map() : Map[Int, Seq[Int]]
    assignments =
      (for (t <- terms) yield {
        (t,
          (if (problem.domains(t).size == 1) {
            termAssIntAux(problem.domains(t).toList(0), problem.bits)
          } else {
            val termStartBit = alloc.alloc(problem.bits)
            val termBits = List.tabulate(problem.bits)(x => x + termStartBit)
            val assBits =
              (for (tt <- problem.domains(t); if tt <= t) yield  {
                termEqIntAux(termBits, tt)
              }).toArray
            solver.addClause(new VecInt(assBits))
            termBits}))}).toMap

    // Enforce idempotency
    for (t <- terms) {
      for (tt <- problem.domains(t); if tt <= t) {
        // Either tt = tt or t != tt
        val iddBit = termEqIntAux(assignments(tt), tt)
        val neqBit = -termEqIntAux(assignments(t), tt)
        solver.addClause(new VecInt(Array(iddBit, neqBit)))
      }
    }
    assignments
  }

  def reorderProblems(goals : Seq[Seq[Seq[(Int, Int)]]]) : Seq[Int] = {
    val count = goals.length
    val order  =
      (for (i <- 0 until count) yield
        (i, goals(i).length)).sortBy(_._2).map(_._1)

    order
  }


  def createBaseDI(terms : Seq[Int], domains : Map[Int, Set[Int]], 
    functions : Seq[(Int, Seq[Int], Int)]) = {
    val size = terms.max + 1
    val arr = Array.ofDim[Int](size, size)
      
    for (t <- terms) {
      val domain = domains.getOrElse(t, List(t))

      for (d <- domain) {
        arr(t)(d) = 1
        arr(d)(t) = 1
      }

      for (tt <- terms; if t != tt) {
        val ttDomain = domains.getOrElse(tt, Set(tt))
        if (domain exists ttDomain) {
          arr(t)(tt) = 1
          arr(tt)(t) = 1
        }
      }
    }

    val baseDI = Array.ofDim[Int](size, size)
    for (t <- terms; tt <- terms)
      baseDI(t)(tt) = arr(t)(tt)

    baseDI
  }

  def createDQ(terms : Seq[Int], domains : Map[Int, Set[Int]], 
    functions : Seq[(Int, Seq[Int], Int)]) = {
    val size = terms.max + 1
    val arr = Array.ofDim[Int](size, size)
      
    for (t <- terms) {
      val domain = domains.getOrElse(t, List(t))

      for (d <- domain) {
        arr(t)(d) = 1
        arr(d)(t) = 1
      }

      for (tt <- terms; if t != tt) {
        val ttDomain = domains.getOrElse(tt, Set(tt))
        if (domain exists ttDomain) {
          arr(t)(tt) = 1
          arr(tt)(t) = 1
        }
      }
    }

    // TODO: Length of disequalities
    val DQ = new Disequalities(size, functions.toArray.map(x => new CCUEq(x)), timeoutChecker)
    
    for (t <- terms; tt <- terms)
      if (arr(t)(tt) == 1) {
        DQ.cascadeRemoveDQ(t,tt)
      }

      // val deq = util.disequalityCheck(c, newFunctions(p))
      // deq
    println("CreatedDQ")
    DQ
  }

  def createProblem[Term, Fun](
    domains : Map[Term, Set[Term]],
    goals : Seq[Seq[Seq[(Term, Term)]]],
    functions : Seq[Seq[(Fun, Seq[Term], Term)]]) : CCUInstance[Term, Fun] = {
    // Timer.measure("createProblem") {
      curId += 1

      val termSet = MSet() : MSet[Term]
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
      // origTerms = terms
      // origDomains = domains
      // origGoals = goals
      // origFunctions = functions

      val bits = util.binlog(terms.length)

      // HACK?
      val problemCount = goals.length


      // Convert to Int representation
      val termToInt = MMap() : MMap[Term, Int]
      val intToTerm = MMap() : MMap[Int, Term]
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

      var funMap = Map() : Map[Fun, Int]
      assigned = 0
      for ((f, _, _) <- functions.flatten) {
        if (!(funMap contains f)) {
          funMap += (f -> assigned)
          assigned += 1
        }
      }

      // Adjust to new representation

      val newTerms = terms.map(termToInt)

      var newDomains = Map() : Map[Int, Set[Int]]
      for (t <- terms) {
        val oldDomain = domains.getOrElse(t, Set())
        if (oldDomain.isEmpty) 
          newDomains += (termToInt(t) -> Set(termToInt(t)))
        else
          newDomains += (termToInt(t) -> oldDomain.map(termToInt))
      }

      val newGoals =
        for (g <- goals)
        yield (for (eqs <- g)
        yield for ((s, t) <- eqs) yield (termToInt(s), termToInt(t)))

      val newFunctions =
        for (funs <- functions)
        yield (for ((f, args, r) <- funs)
        yield (funMap(f), args.map(termToInt), termToInt(r)))

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

      val DQ = (for (p <- 0 until problemCount)
      yield {
        // TODO: Length of disequalities
        val tmpDQ = new Disequalities(newTerms.length, newFunctions(p).toArray.map(x => new CCUEq(x)), timeoutChecker)
        
        // val c = Array.ofDim[Int](newTerms.length, newTerms.length)
        for (t <- newTerms; tt <- newTerms)
          if (arr(t)(tt) == 1) {
            tmpDQ.cascadeRemoveDQ(t,tt)
          }

        // val deq = util.disequalityCheck(c, newFunctions(p))
        // deq
        tmpDQ
      })

      val baseDI = (for (p <- 0 until problemCount)
      yield {
        val c = Array.ofDim[Int](newTerms.length, newTerms.length)
        for (t <- newTerms; tt <- newTerms)
          c(t)(tt) = arr(t)(tt)

        arr
        // val deq = util.disequalityCheck(c, newFunctions(p))
        // deq-
      })

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

          val fd =
            (for ((t, d) <- newDomains; if (ft contains t)) yield {
              (t, d.filter(x => ft contains x))
            }).toMap
          // val fd = newDomains
          (ff, ft, fd)
        }) : Seq[(Seq[(Int, Seq[Int], Int)], Seq[Int], Map[Int, Set[Int]])]

      val filterTerms = for ((_, ft, _) <- ffs) yield ft
      val filterDomains = for ((_, _, fd) <- ffs) yield fd
      val filterFunctions = for ((ff, _, _) <- ffs) yield ff

      val order = reorderProblems(newGoals)

      for (fd <- filterDomains) {
        for ((k, v) <- fd) {
          if (v.isEmpty) {
            println("domains: " + domains)
            println("goals: " + goals)
            println("functions: " + functions)
            println("ffs: " + ffs)
            println("filterDomains: " + filterDomains)
            throw new Exception("CreateProblem, empty domain")
          }
        }
      }

      // TODO: FIX!

      val reorderTerms = (for (i <- order) yield filterTerms(i))
      val reorderDomains = (for (i <- order) yield filterDomains(i))
      val reorderGoals = (for (i <- order) yield newGoals(i))
      val reorderFunctions = 
        (for (i <- order) yield filterFunctions(i).map(x => new CCUEq(x)))
      val reorderDQ = (for (i <- order) yield DQ(i))
      val reorderBaseDI = (for (i <- order) yield baseDI(i))

      val problems = 
        for (i <- 0 until problemCount) yield
          new CCUSubProblem(reorderTerms(i), reorderDomains(i), 
            reorderFunctions(i), new CCUGoal(reorderGoals(i)),
            reorderBaseDI(i), reorderDQ(i))

      // val newDiseq = 
      //   for (d <- reorderDiseq) yield {
      //     val newD = Array.ofDim[Int](d.length * d.length)
      //     for (i <- 0 until d.length; j <- 0 until d.length) {
      //       newD(i * d.length + j) = d(i)(j)
      //     }
      //     newD
      //   }

      val problem = 
        new CCUSimProblem(
          newTerms,
          newDomains,
          bits,
          // reorderDiseq,
          // newDiseq,
          // reorderBaseDI,
          order,
          problems)

      // TODO: Fix immutable map
      new CCUInstance[Term, Fun](curId, this, problem, termToInt.toMap)
    // }
  }


  def createInstanceFromFile[Fun, Term](filename : String) = {
    curId += 1

    val fis = new FileInputStream(filename)
    val ois = new ObjectInputStream(fis)

    val o = ois.readObject
    val problem = (o match {
      case p : CCUSimProblem => p
      case _ => throw new Exception("Couldn't parse " + filename + ": not a CCU-problem")
    })

    ois.close
    fis.close

    new CCUInstance[Term, Fun](curId, this, problem, Map())
  }

  def createInstanceFromJson[Fun, Term](filename : String) = {
    curId += 1

    val lines = scala.io.Source.fromFile(filename).getLines
    val json = lines.next

    // println("Parsing JSON: " + json)

    implicit def CCUGoalDecodeJson: DecodeJson[CCUGoal] = 
      DecodeJson(c => for {
        subGoals <- (c --\ "subGoals").as[List[List[(Int,Int)]]]
      } yield new CCUGoal(subGoals))

    implicit def CCUEqDecodeJson: DecodeJson[CCUEq] = 
      DecodeJson(c => for {
        fun <- (c --\ "fun").as[Int]
        args <- (c --\ "args").as[List[Int]]
        res <- (c --\ "res").as[Int]
      } yield new CCUEq((fun, args, res)))

    // HERE IS THE PROBLEM, need SUPERCLASS lenght of terms!

    implicit def CCUSubProblemDecodeJson: DecodeJson[CCUSubProblem] = 
      DecodeJson(c => for {
        terms <- (c --\ "terms").as[List[Int]]
        domains <- (c --\ "domains").as[List[(Int,List[Int])]]
        funEqs <- (c --\ "funEqs").as[List[CCUEq]]
        goal <- (c --\ "goal").as[CCUGoal]
      } yield new CCUSubProblem(terms, 
        (for ((k, v) <- domains) yield (k, v.toSet)).toMap, 
        funEqs, 
        goal, 
        createBaseDI(terms, (for ((k, v) <- domains) yield (k, v.toSet)).toMap, funEqs.map(_.eq)),
        createDQ(terms, (for ((k, v) <- domains) yield (k, v.toSet)).toMap, funEqs.map(_.eq))))


    implicit def CCUSimProblemDecodeJson: DecodeJson[CCUSimProblem] =
      DecodeJson(c => for {
        terms <- (c --\ "terms").as[List[Int]]
        domains <- (c --\ "domains").as[List[(Int,List[Int])]]
        bits <- (c --\ "bits").as[Int]
        order <- (c --\ "order").as[List[Int]]
        subProblems <- (c --\ "subProblem").as[List[CCUSubProblem]]
      } yield new CCUSimProblem(terms, 
        (for ((k, v) <- domains) yield (k, v.toSet)).toMap, 
        bits, order, subProblems))

    // TODO: error handling
    val res = json.decodeEither[CCUSimProblem]
    // println(res)

    val problem = json.decodeOption[CCUSimProblem].get


    // for (p <- 0 until problem.size) {
    //   val uf = util.CCunionFind(problem.terms, problem(p).funEqs, List())
    //   val c = Array.ofDim[Int](problem.terms.length, problem.terms.length)
    //   for (t <- problem.terms; tt <- problem.terms)
    //     if (uf(t) == uf(tt)) {
    //       c(t)(tt) = 1
    //     } else
    //       c(t)(tt) = 0
    //   problem(p).baseDI = c
    // }

    new CCUInstance[Term, Fun](curId, this, problem, Map())
  }

  def checkSAT[Term, Fun](
    terms : Seq[Term],
    domains : Map[Term, Set[Term]],
    goals : Seq[Seq[Seq[(Term, Term)]]],
    functions : Seq[Seq[(Fun, Seq[Term], Term)]],
    solution : Map[Term, Term]) : Boolean = {

    val sets = MSet() : MSet[Set[Term]]
    for (t <- terms)
      sets += Set(t)

    def set(t : Term) : Set[Term] = {
      for (s <- sets)
        if (s contains t)
          return s
      throw new Exception("No set contains t?")
    }


    // for (p <- 0 until goals.length)
    //   if (!verifySolution(terms, solution, functions(p), goals(p)))
    //     return false

    true
  }

  def checkUNSAT[Term, Fun](
    terms : Seq[Term],
    domains : Map[Term, Set[Term]],
    goals : Seq[Seq[Seq[(Term, Term)]]],
    functions : Seq[Seq[(Fun, Seq[Term], Term)]]) : Boolean = {
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
      def formSolutions(dom : Seq[Seq[(Term, Term)]], sol : Map[Term, Term])
          : Option[Map[Term, Term]] = {
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
        // TODO!
        // for ((k,v) <- sol)
        //   println("\t" + termToInt(k) + " := " + termToInt(v))
        false
      } else {
        true
      }
    }
  }


  //
  //   CONSTRUCTOR METHOD BEGIN
  //

  val util = new Util(timeoutChecker)
  val alloc = new Allocator
  val ZEROBIT = 1
  val ONEBIT = 2

  // TODO: Make real bound?
  val solver = SolverFactory.newDefault()
  val MAXVAR = 1000000;
  solver.newVar (MAXVAR);
  solver.setTimeoutMs(maxSolverRuntime)
  val gt = new GateTranslator(solver)

}

