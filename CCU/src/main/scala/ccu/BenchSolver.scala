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
    val tresult = tsolver.solveaux(problem)
    val lresult = lsolver.solveaux(problem)

    println("Table solver: " + tresult)
    println("Lazy solver: " + lresult)

    println(tsolver.S)
    println(lsolver.S)

    tresult

  }

  // We automatically calculate unsatCore
  var lastUnsatCore = List() : Seq[Int]


  def unsatCoreAux(problem : CCUSimProblem, timeout : Int) = {
    lastUnsatCore
  }
}
