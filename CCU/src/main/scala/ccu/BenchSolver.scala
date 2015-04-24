package ccu;

import org.sat4j.tools.GateTranslator
import org.sat4j.minisat.SolverFactory
import org.sat4j.specs.ISolver
import org.sat4j.core.VecInt

import argonaut._, Argonaut._
import scalaz._, Scalaz._

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



    implicit def CCUGoalEncodeJson: EncodeJson[CCUGoal] = 
      EncodeJson((g : CCUGoal) =>
        ("subGoals" := g.subGoals.map(_.toList).toList) ->: jEmptyObject)

    implicit def CCUEqEncodeJson: EncodeJson[CCUEq] = 
      EncodeJson((eq : CCUEq) =>
        ("fun" := eq.eq._1) ->: ("args" := eq.eq._2.toList) ->: 
          ("res" := eq.eq._3) ->: jEmptyObject)

    implicit def CCUSubProblemEncodeJson: EncodeJson[CCUSubProblem] = 
      EncodeJson((sp: CCUSubProblem) =>
        ("terms" := sp.terms.toList) ->: ("domains" := sp.domains.toList) ->:  
          ("funEqs" := sp.funEqs.toList) ->: ("goal" := sp.goal) ->: jEmptyObject)

    implicit def CCUSimProblemEncodeJson: EncodeJson[CCUSimProblem] =
      EncodeJson((p: CCUSimProblem) =>
        ("terms" := p.terms.toList) ->: ("domains" := p.domains.toList) ->:  
          ("bits" := p.bits) ->: ("order" := p.order.toList) ->: 
          ("subProblem" := p.subProblems.toList) ->: jEmptyObject)


    def handleTimeout = {
      println("---TIMEOUTPROBLEM---")
      val json = problem.asJson.toString
      println(json)
      println("---ENDTIMEOUTPROBLEM---")
    }


    val (tresult, ttime) = 
      try {
        time { Timer.measure("TableSolver") { tsolver.solveaux(problem) } }
      } catch {
        case (e : Exception) =>
          if (e.getClass.toString == "class ap.util.Timeout")
            handleTimeout

          throw e
      }

    val (lresult, ltime) = 
      try {
        time { Timer.measure("LazySolver") { lsolver.solveaux(problem) } }
      } catch {
        case (e : Exception) =>
          if (e.getClass.toString == "class ap.util.Timeout")
            handleTimeout

          throw e
      }



    println("---NEW PROBLEM---")
    println("ID:" + scala.util.Random.nextInt(2147483647))
    println("SIZE:" + problem.size)
    println("TERMS:" + problem.terms.length)
    println("MAXFUN:" + (for (p <- problem.subProblems) yield p.funEqs.length).max)
    println("MAXGOAL:" + (for (p <- problem.subProblems) yield p.goal.subGoals.length).max)

    val json = problem.asJson.toString

    println(problem)
    println(json)

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
