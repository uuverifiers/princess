package ccu;

import org.sat4j.core._
import org.sat4j.specs._
import org.sat4j.minisat._
import org.sat4j.tools._

import java.io.FileInputStream
import java.io.ObjectInputStream
import java.io.File

// import argonaut._, Argonaut._
// import scalaz._, Scalaz._


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
abstract class CCUSolver[Term, Fun](
  val timeoutChecker : () => Unit,
  val maxSolverRuntime : Long) {

  type FunApp = (Fun, Seq[Term], Term)
  type Goal = (Term, Term)

  type IntFunApp = (Int, Seq[Int], Int)
  type IntGoal = (Int, Int)

  
  //
  //   CONSTRUCTOR METHOD BEGIN
  //

  val alloc = new Allocator
  val ZEROBIT = 1
  val ONEBIT = 2

  // TODO: Make real bound?
  val solver = SolverFactory.newDefault()
  val MAXVAR = 1000000;
  solver.newVar(MAXVAR);
  solver.setTimeoutMs(maxSolverRuntime)
  val gt = new GateTranslator(solver)

  val S = new Stats
  var curId = 0
  var previousInstance = None : Option[CCUInstance[Term, Fun]]

  def getStat(result : ccu.Result.Result) : String

  def solve(problem : CCUSimProblem, asserted : Boolean) = 
  Timer.measure("CCUSolver.solve") {
    // println("CCUSolver.solve")


    val result =
      // if (problem.solvable == false) {
      //   println("\tDisequality check")
      //   // println(problem)
      //   (ccu.Result.UNSAT, None)
      // } else { 
        solveaux(problem)
      // }

    // println("\tChecking solution")
    if (asserted) {
      result match {
        case (ccu.Result.SAT, Some(model)) => {
          if (!problem.verifySolution(model)) {
            // println(problem)
            // println("Model: " + model)
            // println(problem.JSON)
            throw new Exception("False SAT")
          } else {
            // println("\t\tSAT asserted")
            (ccu.Result.SAT, Some(model))
          }
        }
        case (ccu.Result.UNSAT, _) => {
          // println("\t\tUNSAT *not* asserted")
          (ccu.Result.UNSAT, None)
        }
        case _ => throw new Exception("Strange result from solve!")
      }
    } else {
      result
    }
  }

  def unsatCore(problem : CCUSimProblem, timeout : Int) = {
    val core =
      unsatCoreAux(problem, timeout)
    assert(!core.isEmpty)
    (for (p <- core) yield (problem.order(p)))
  }

  // Asbtract functions
  protected def solveaux(problem : CCUSimProblem) : 
      (Result.Result, Option[Map[Int, Int]])

  def unsatCoreAux(problem : CCUSimProblem, timeout : Int) : Seq[Int]

  def reset = {
    solver.reset()
    alloc.reset
    solver.setTimeoutMs(maxSolverRuntime)
    solver.addClause(new VecInt(Array(-ZEROBIT)))
    solver.addClause(new VecInt(Array(ONEBIT)))
    S.clear
  }

  def assignmentsToSolution[Term](assignments : Map[Int, Seq[Int]]) = {
    // If bit B is true, bitArray(bitMap(B)) should be true
    var bitMap = Map() : Map[Int, List[Int]]

    // Prune all bits that are not with var ass and put in bitArray
    // (assuming all terms are represented by the same number of bits)
    var bitArray =
      Array.ofDim[Boolean](assignments.size * assignments.head._2.size)

    // Current position in bitArray
    var curPos = 0

    // Term T can find its bits in resultMap(T)
    val resultMap = 
      (for ((term, bits) <- assignments) yield {
        val newResult =
          (for (i <- 0 until bits.length) yield {
            val newList = curPos :: (bitMap.getOrElse(bits(i), List()))
            bitMap += (bits(i) -> newList)
            curPos += 1
            (curPos - 1)
          })
        term -> newResult
      })    

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

    (for (t <- assignments.keys) yield t -> bitToInt2(resultMap(t))).toMap
  }

  // def verifySolution(
  //   terms : Seq[Int],
  //   assignment : Map[Int,Int],
  //   functions : Seq[CCUEq],
  //   goal : CCUGoal)
  //     : Boolean = {

  //   val uf = Util.CCunionFind(terms, functions, assignment.toList)

  //   var satisfiable = false

  //   for (subGoal <- goal.subGoals) {
  //     var subGoalSat = true

  //     var allPairsTrue = true
  //     for ((s,t) <- subGoal) {
  //       if (uf(s) != uf(t)) {
  //         allPairsTrue = false
  //       }

  //       if (!allPairsTrue)
  //         subGoalSat = false
  //     }
  //     if (subGoalSat) {
  //       satisfiable = true
  //     }
  //   }
  //   satisfiable
  // }

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

  def reorderProblems(terms : Seq[Seq[Int]], domains : Seq[Map[Int,Set[Int]]],
    functions : Seq[Seq[(Int, Seq[Int], Int)]], goals : Seq[Seq[Seq[(Int, Int)]]]) : Seq[Int] = {
    val count = goals.length

    // 
    // Order by goals length (Increasing)
    //
    // val order  =
    //   (for (i <- 0 until count) yield
    //     (i, goals(i).length)).sortBy(_._2).map(_._1)

    // 
    // Order by goals length (Decreasing)
    //
    // BEST SO FAR?
    //

    val order  =
      (for (i <- 0 until count) yield
        (i, goals(i).length)).sortBy(_._2).map(_._1).reverse

    //
    // Order by function count (Increasing)
    //
    // val order = 
    //   (for (i <- 0 until count) yield
    //     (i, functions(i).length)).sortBy(_._2).map(_._1).reverse

    //
    // Order by total domain size (Increasing)
    //
    // val order = 
    //   (for (i <- 0 until count) yield
    //     (i, ((for ((t, d) <- domains(i)) yield d.size).sum))).sortBy(_._2).map(_._1)

    //
    // Order by term count (Increasing)
    //
    // val order = 
    //   (for (i <- 0 until count) yield
    //     (i, terms(i).length)).sortBy(_._2).map(_._1)


    order
  }

  def createDQ(terms : Seq[Int],
    domains : Map[Int, Set[Int]],
    functions : Seq[(Int, Seq[Int], Int)]) = {

    val size = if (terms.isEmpty) 0 else (terms.max + 1)
    // Store all disequalities that always must hold!

    val DQ = new Disequalities(size, functions.map(x => CCUEq(x)).toArray, timeoutChecker)
    for (t <- terms) {
      val domain = domains.getOrElse(t, List(t))

      for (d <- domain) {
        DQ.cascadeRemove(t, d)
      }

      for (tt <- terms; if t != tt) {
        val ttDomain = domains.getOrElse(tt, Set(tt))
        if (domain exists ttDomain) {
          DQ.cascadeRemove(t, tt)
        }
      }
   }

    DQ
  }

  def createBaseDQ(
    terms : Seq[Int],
    domains : Map[Int, Set[Int]],
    functions : Seq[(Int, Seq[Int], Int)]) = {
    val size = if (terms.isEmpty) 0 else (terms.max + 1)
    // Store all disequalities that always must hold!

    val baseDQ = new Disequalities(size, functions.map(x => CCUEq(x)).toArray, timeoutChecker)
    for (t <- terms) {
      val domain = domains.getOrElse(t, List(t))

      for (d <- domain) {
        baseDQ.remove(t, d)
      }

      for (tt <- terms; if t != tt) {
        val ttDomain = domains.getOrElse(tt, Set(tt))
        if (domain exists ttDomain)
          baseDQ.remove(t, tt)
      }
    }

    baseDQ
  }

  private def extractTerms(domains : Map[Term, Set[Term]],
    functions : Seq[FunApp],
    goals : Seq[Seq[Goal]]) = {

    val termSet = MSet() : MSet[Term]
    for ((_, d) <- domains)
      for (t <- d)
        termSet += t
    for ((s,t) <- goals.flatten) {
      termSet += s
      termSet += t
    }
    for ((_, args, r) <- functions) {
      for (t <- args)
        termSet += t
      termSet += r
    }
    
    termSet.toSet
  }

  private def intExtractTerms(domains : Map[Int, Set[Int]],
    functions : Seq[IntFunApp],
    goals : Seq[Seq[IntGoal]]) : Set[Int] = {

    val termSet = MSet() : MSet[Int]
    for ((_, d) <- domains)
      for (t <- d)
        termSet += t
    for ((s,t) <- goals.flatten) {
      termSet += s
      termSet += t
    }
    for ((_, args, r) <- functions) {
      for (t <- args)
        termSet += t
      termSet += r
    }
    
    termSet.toSet
  }


  private def createTermMapping(
    terms : Seq[Term],
    domains : Map[Term, Set[Term]])
      : (Map[Term, Int], Map[Int, Term]) = {

    // Convert to Int representation
    val termToInt = MMap() : MMap[Term, Int]
    val intToTerm = MMap() : MMap[Int, Term]
    var assigned = 0

    while (assigned < terms.length) {
      for (t <- terms) {
        if (!(termToInt contains t)) {
          // Assign term after its domain is assigned (well-ordering)
          val d = domains.getOrElse(t, Set()).filter(_ != t)
          val dass = d.map(termToInt contains _)
          if (dass.forall(_ == true)) {
            termToInt += (t -> assigned)
            intToTerm += (assigned -> t)
            assigned += 1
          }
        }
      }
    }

    (termToInt.toMap, intToTerm.toMap)
  }


  private def createFunMapping(
    functions : Seq[Seq[FunApp]]
  ) : Map[Fun, Int] = {
    var assigned = 0
    var funMap = Map() : Map[Fun, Int]
    for ((f, _, _) <- functions.flatten) {
      if (!(funMap contains f)) {
        funMap += (f -> assigned)
        assigned += 1
      }
    }
    funMap
  }

  // Create a problem from internal (Integer) representation
  def intCreateProblem(
    domains : Map[Int, Set[Int]],
    subProblems : Seq[(Seq[Seq[IntGoal]], Seq[IntFunApp])]) : CCUSimProblem = {

    val problemCount = subProblems.length
    val termSets = 
      for (p <- 0 until problemCount) yield
        intExtractTerms(domains, subProblems(p)._2, subProblems(p)._1)

    val allTerms = (termSets.:\(Set() : Set[Int])(_ ++ _)).toList
    val bits = Util.binlog(allTerms.length)

    val arr = Array.ofDim[Int](allTerms.length, allTerms.length)

    val ffs =
      (for (p <- 0 until problemCount) yield {
        val (goals, functions) = subProblems(p)
        // Filter terms per table
        def isUsed(term : Int, funs : Seq[(Int, Seq[Int], Int)],
          goals : Seq[Seq[(Int, Int)]]) : Boolean = {
          for ((_, args, s) <- funs) {
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

        val ff = functions


        val tmpFt = ListBuffer() : ListBuffer[Int]
        for (t <- (allTerms.filter(x => isUsed(x, ff, goals))))
          tmpFt += t

        // We have to add all terms that are in the domains of ft
        var ftChanged = true
        while (ftChanged) {
          ftChanged = false
          for (t <- tmpFt) {
            for (tt <- domains(t)) {
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
          (for ((t, d) <- domains; if (ft contains t)) yield {
            (t, d.filter(x => ft contains x))
          }).toMap
        // val fd = newDomains
        val fg = goals
        (ff, ft, fd, fg)
      }) : Seq[(Seq[(Int, Seq[Int], Int)], Seq[Int], Map[Int, Set[Int]], Seq[Seq[IntGoal]])]

    val filterTerms = for ((_, ft, _, _) <- ffs) yield ft
    val filterDomains = for ((_, _, fd, _) <- ffs) yield fd
    val filterFunctions = for ((ff, _, _, _) <- ffs) yield ff
    val filterGoals = for ((_, _, _, fg) <- ffs) yield fg

    val DQ =
      for (p <- 0 until problemCount)
      yield createDQ(
        filterTerms(p),
        filterDomains(p),
        filterFunctions(p))

    val baseDQ =
      for (p <- 0 until problemCount)
      yield createBaseDQ(
        filterTerms(p),
        filterDomains(p),
        filterFunctions(p))

    val order = reorderProblems(filterTerms, filterDomains, filterFunctions, filterGoals)

    val reorderTerms = (for (i <- order) yield filterTerms(i))
    val reorderDomains = (for (i <- order) yield filterDomains(i))
    val reorderGoals = (for (i <- order) yield filterGoals(i))
    val reorderFunctions =
      (for (i <- order) yield filterFunctions(i).map(x => new CCUEq(x)))
    val reorderDQ = (for (i <- order) yield DQ(i))
    val reorderBaseDQ = (for (i <- order) yield baseDQ(i))


    val problems =
      for (i <- 0 until problemCount) yield
        new CCUSubProblem(reorderTerms(i), reorderDomains(i),
          reorderFunctions(i), new CCUGoal(reorderGoals(i)),
          reorderDQ(i), reorderBaseDQ(i))

    new CCUSimProblem(
      allTerms,
      domains,
      bits,
      order,
      problems)
  }


  def createProblem(
    domains : Map[Term, Set[Term]],
    goals : Seq[Seq[Seq[Goal]]],
    functions : Seq[Seq[FunApp]],
    negFunctions : Seq[Seq[FunApp]]) : CCUInstance[Term, Fun] = {

    curId += 1
    val problemCount = goals.length
    val triplets = for (i <- 0 until problemCount) yield { (goals(i), functions(i), negFunctions(i)) }

    //
    // Convert to Int representation
    //
    val termSets = 
      for (p <- 0 until problemCount) yield
        extractTerms(domains, functions(p) ++ negFunctions(p), goals(p))

    val allTerms = (termSets.:\(Set() : Set[Term])(_ ++ _)).toList
    val terms = for (p <- 0 until problemCount) yield allTerms
    val bits = Util.binlog(allTerms.length)


    val (termToInt, intToTerm) = createTermMapping(allTerms, domains)
    val funMap = createFunMapping(functions ++ negFunctions)
    val intAllTerms = allTerms.map(termToInt)

    // Each term is added to its own domain
    // TODO: http://stackoverflow.com/questions/1715681/scala-2-8-breakout/1716558#1716558
    val newDomains = 
      (for (t <- allTerms) yield {
        val oldDomain = domains.getOrElse(t, Set(t))
        (termToInt(t) -> oldDomain.map(termToInt))
      }).toMap


    // 
    // Convert each subproblem
    // + to integer representation
    // + change NegFunEquations to goals

    // Conversion might introduce new terms, nextTerm shows next available term
    // Increasing by one allocates one new term (which is added to domain, etc.)
    var nextTerm = if (intAllTerms.length > 0) intAllTerms.max + 1 else 0

    val subProblems = 
      for ((goals, funs, negFuns) <- triplets) yield {

        val extraFunctions = ListBuffer() : ListBuffer[IntFunApp]
        val extraGoals = ListBuffer() : ListBuffer[Seq[IntGoal]]

        val negFunGoals = for (nf <- negFuns) yield {
          // Convert f(args) != r to new FunEq f(args) = t and new Goal (t = r) where t is a fresh term
          val (f, args, r) = nf

          val t = nextTerm
          nextTerm += 1
          val newFun = (funMap(f), args.map(termToInt), t)
          val newGoal = (t, termToInt(r))

          extraFunctions += newFun
          extraGoals += List(newGoal)

          println("NegativeFunApp " + nf + " converted to " + newFun + " and " + newGoal)
        }

        val newGoals = (for (eqs <- goals) yield for ((s, t) <- eqs) yield (termToInt(s), termToInt(t))) ++ extraGoals
        val newFunctions = (for ((f, args, r) <- funs) yield (funMap(f), args.map(termToInt), termToInt(r))) ++ extraFunctions

        // val newNegFunctions =
        //   for (negFuns <- negFunctions)    
        //   yield (for ((f, args, r) <- negFuns)
        //   yield (funMap(f), args.map(termToInt), termToInt(r)))
        (newGoals, newFunctions)
      }

    val problem = intCreateProblem(newDomains, subProblems)

    new CCUInstance[Term, Fun](curId, this, problem, termToInt.toMap,
                               domains)
  }

  def createProblem(
    domains : Map[Term, Set[Term]],
    goals : Seq[Seq[Seq[Goal]]],
    functions : Seq[Seq[FunApp]]) : CCUInstance[Term, Fun] = createProblem(domains, goals, functions, for (_ <- goals) yield List())


  // def createInstanceFromJson[Fun, Term](filename : String) = {
  //   curId += 1

  //   val lines = scala.io.Source.fromFile(filename).getLines
  //   val json = lines.next

  //   implicit def CCUGoalDecodeJson: DecodeJson[CCUGoal] =
  //     DecodeJson(c => for {
  //       subGoals <- (c --\ "subGoals").as[List[List[(Int,Int)]]]
  //     } yield new CCUGoal(subGoals))

  //   implicit def CCUEqDecodeJson: DecodeJson[CCUEq] =
  //     DecodeJson(c => for {
  //       fun <- (c --\ "fun").as[Int]
  //       args <- (c --\ "args").as[List[Int]]
  //       res <- (c --\ "res").as[Int]
  //     } yield new CCUEq((fun, args, res)))

  //   // HERE IS THE PROBLEM, need SUPERCLASS lenght of terms!

  //   implicit def CCUSubProblemDecodeJson: DecodeJson[CCUSubProblem] =
  //     DecodeJson(c => for {
  //       terms <- (c --\ "terms").as[List[Int]]
  //       domains <- (c --\ "domains").as[List[(Int,List[Int])]]
  //       funEqs <- (c --\ "funEqs").as[List[CCUEq]]
  //       goal <- (c --\ "goal").as[CCUGoal]
  //     } yield new CCUSubProblem(terms,
  //       (for ((k, v) <- domains) yield (k, v.toSet)).toMap,
  //       funEqs,
  //       goal,
  //       createBaseDQ(terms, (for ((k, v) <- domains) yield (k, v.toSet)).toMap, funEqs.map(_.eq)),
  //       createBaseDQ(terms, (for ((k, v) <- domains) yield (k, v.toSet)).toMap, funEqs.map(_.eq))))

  //   implicit def CCUSimProblemDecodeJson: DecodeJson[CCUSimProblem] =
  //     DecodeJson(c => for {
  //       terms <- (c --\ "terms").as[List[Int]]
  //       domains <- (c --\ "domains").as[List[(Int,List[Int])]]
  //       bits <- (c --\ "bits").as[Int]
  //       order <- (c --\ "order").as[List[Int]]
  //       subProblems <- (c --\ "subProblem").as[List[CCUSubProblem]]
  //     } yield new CCUSimProblem(terms,
  //       (for ((k, v) <- domains) yield (k, v.toSet)).toMap,
  //       bits, order, subProblems))

  //   val problem = json.decodeOption[CCUSimProblem].get

  //   new CCUInstance(curId, this, problem, Map())
  // }
}

