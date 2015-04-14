package ccu;

import org.sat4j.tools.GateTranslator
import org.sat4j.minisat.SolverFactory
import org.sat4j.specs.ISolver
import org.sat4j.core.VecInt

import scala.collection.mutable.{Set => MSet}


class BenchSolver(timeoutChecker : () => Unit, 
                              maxSolverRuntime : Long)  
    extends CCUSolver(timeoutChecker, maxSolverRuntime) {

  val tsolver = new TableSolver(timeoutChecker, maxSolverRuntime)
  val lsolver = new LazySolver(timeoutChecker, maxSolverRuntime)


  override def solveaux(problem : CCUSimProblem) : (ccu.Result.Result, Option[Map[Int, Int]]) = {
    reset


    def time[R](block: => R): (R, Int) = {
      val t0 = System.nanoTime()
      val result = block
      val t1 = System.nanoTime()
      (result, ((t1 - t0)/1000000).toInt)
    }

    val (tresult, ttime) = time { Timer.measure("TableSolver") { tsolver.solveaux(problem) } }
    val (lresult, ltime) = time { Timer.measure("LazySolver") { lsolver.solveaux(problem) } }

    println("---NEW PROBLEM---")
    println("ID:" + scala.util.Random.nextInt(2147483647))

    println(problem)

    println(tsolver.S + ",TIME:" + ttime)
    println(lsolver.S + ",TIME:" + ltime)
    println("---END PROBLEM---")
    if (tresult._1 != lresult._1)
      throw new Exception("Different Results!")

    tresult


  }

  // We automatically calculate unsatCore
  var lastUnsatCore = List() : Seq[Int]


  def unsatCoreAux(problem : CCUSimProblem, timeout : Int) = {
    tsolver.unsatCore(problem, timeout)
  }
}
