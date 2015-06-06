package ccu;

import org.sat4j.tools.GateTranslator
import org.sat4j.minisat.SolverFactory
import org.sat4j.specs.ISolver
import org.sat4j.core.VecInt



import scala.collection.mutable.{Set => MSet}

case class BenchTimeoutException(msg : String) extends RuntimeException(msg)

object BenchSolver {
  val TIMEOUT = 10000 : Long
  var startTime = System.currentTimeMillis()
  def customTimeoutChecker(timeout : Long)() = {
    if (System.currentTimeMillis() - startTime >= timeout) {
      throw new BenchTimeoutException("Bench Timeout")
    }
  }
}

class BenchSolver[Term, Fun](timeoutChecker : () => Unit, 
                              maxSolverRuntime : Long)  
    extends CCUSolver[Term, Fun](BenchSolver.customTimeoutChecker(BenchSolver.TIMEOUT), maxSolverRuntime) {


  override def getStat(res : ccu.Result.Result) = { res.toString }

  override def createProblem(
    domains : Map[Term, Set[Term]],
    goals : Seq[Seq[Seq[(Term, Term)]]],
    functions : Seq[Seq[(Fun, Seq[Term], Term)]]) : CCUInstance[Term, Fun] = {
    BenchSolver.startTime = System.currentTimeMillis()
    super.createProblem(domains, goals, functions)
  }

  def time[R](block: => R): (R, Int) = {
    val t0 = System.nanoTime()
    val result = block
    val t1 = System.nanoTime()
    (result, ((t1 - t0)/1000000).toInt)
  }

  def debugPrint(problem : CCUSimProblem) = {
    println("---NEW PROBLEM---")
    println("ID:" + scala.util.Random.nextInt(2147483647))
    println("SIZE:" + problem.size)
    println("TERMS:" + problem.terms.length)
    println("MAXFUN:" + (for (p <- problem.subProblems) yield p.funEqs.length).max)
    println("MAXGOAL:" + (for (p <- problem.subProblems) yield p.goal.subGoals.length).max)

    println(problem)
    println(problem.JSON)

    println("---END PROBLEM---")
  }

  override def solveaux(problem : CCUSimProblem) : (ccu.Result.Result, Option[Map[Int, Int]]) = {
    reset

    println("Solving")
    val (tresult, ttime) = 
      try {
        println("Running Tablesolver...")
        BenchSolver.startTime = System.currentTimeMillis()
        time { Timer.measure("TableSolver") { 
          tsolver.solveaux(problem) 
        } }
      } catch {
        case (e : BenchTimeoutException) =>
          println("Table timeout!")
          ((ccu.Result.UNKNOWN, None), BenchSolver.TIMEOUT)
      }
    println("\tTable: " + tresult._1)

    val (lresult, ltime) = 
      try {
        println("Running Lazysolver...")
        BenchSolver.startTime = System.currentTimeMillis()
        time { Timer.measure("LazySolver") { lsolver.solveaux(problem) } }
      } catch {
        case (e : BenchTimeoutException) =>
          ((ccu.Result.UNKNOWN, None), BenchSolver.TIMEOUT)
      }
    println("\tLazy: " + lresult._1)
    println("\tLazy model: " + lresult._2)

    debugPrint(problem)
    println(tsolver.getStat(tresult._1) + ",TIME:" + ttime)
    println(lsolver.getStat(lresult._1) + ",TIME:" + ltime)

    (tresult._1, lresult._1) match {
      case (ccu.Result.UNKNOWN, ccu.Result. UNKNOWN) => tresult
      case (ccu.Result.UNKNOWN, _) => lresult
      case (_, ccu.Result.UNKNOWN) => tresult
      case (ccu.Result.SAT, ccu.Result.SAT) => tresult
      case (ccu.Result.UNSAT, ccu.Result.UNSAT) => tresult
      case _ => throw new Exception("Different Results!")

    }
  }

  def unsatCoreAux(problem : CCUSimProblem, timeout : Int) = {
    lsolver.unsatCore(problem, timeout)
  }

  // println("Creating BenchSolver...")
  BenchSolver.startTime = System.currentTimeMillis()
  val tsolver = new TableSolver(BenchSolver.customTimeoutChecker(BenchSolver.TIMEOUT), maxSolverRuntime)
  // println("\ttable solver")
  BenchSolver.startTime = System.currentTimeMillis()
  val lsolver = new LazySolver(BenchSolver.customTimeoutChecker(BenchSolver.TIMEOUT), maxSolverRuntime)
  // println("\tlazy solver")

}
