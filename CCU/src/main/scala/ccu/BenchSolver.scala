package ccu;

import org.sat4j.tools.GateTranslator
import org.sat4j.minisat.SolverFactory
import org.sat4j.specs.ISolver
import org.sat4j.core.VecInt

import argonaut._, Argonaut._
import scalaz._, Scalaz._

import scala.collection.mutable.{Set => MSet}

case class BenchTimeoutException(msg : String) extends RuntimeException(msg)


object BenchSolver {
  val TIMEOUT = 60000 : Long
  var startTime = System.currentTimeMillis()
  def customTimeoutChecker(timeout : Long)() = {
    if (System.currentTimeMillis() - startTime >= timeout) {
      throw new BenchTimeoutException("Bench Timeout")
    }
  }
}

class BenchSolver(timeoutChecker : () => Unit, 
                              maxSolverRuntime : Long)  
    extends CCUSolver(BenchSolver.customTimeoutChecker(BenchSolver.TIMEOUT), maxSolverRuntime) {

  BenchSolver.startTime = System.currentTimeMillis()
  val tsolver = new TableSolver(BenchSolver.customTimeoutChecker(BenchSolver.TIMEOUT), maxSolverRuntime)

  BenchSolver.startTime = System.currentTimeMillis()
  val lsolver = new LazySolver(BenchSolver.customTimeoutChecker(BenchSolver.TIMEOUT), maxSolverRuntime)

  override def createProblem[Term, Fun](
    domains : Map[Term, Set[Term]],
    goals : Seq[Seq[Seq[(Term, Term)]]],
    functions : Seq[Seq[(Fun, Seq[Term], Term)]]) : CCUInstance[Term, Fun] = {
    BenchSolver.startTime = System.currentTimeMillis()
    super.createProblem[Term, Fun](domains, goals, functions)
  }

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
      println("---BenchSolver.TIMEOUTPROBLEM---")
      val json = problem.asJson.toString
      println(json)
      println("---ENDBenchSolver.TIMEOUTPROBLEM---")
    }


    val (tresult, ttime) = 
      try {
        println("Running Tablesolver...")
        BenchSolver.startTime = System.currentTimeMillis()
        time { Timer.measure("TableSolver") { tsolver.solveaux(problem) } }
      } catch {
        case (e : BenchTimeoutException) =>
          // handleTimeout
          // throw new Timeout("Bench T/O")
          println("Table timeout!")
          ((ccu.Result.UNKNOWN, None), BenchSolver.TIMEOUT)
      }

    val (lresult, ltime) = 
      try {
        println("Running Lazysolver...")
        BenchSolver.startTime = System.currentTimeMillis()
        time { Timer.measure("LazySolver") { lsolver.solveaux(problem) } }
      } catch {
        case (e : BenchTimeoutException) =>
          println("Lazy timeout!")
          ((ccu.Result.UNKNOWN, None), BenchSolver.TIMEOUT)

        //   handleTimeout
        //   throw new Timeout("Bench T/O")
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

    (tresult._1, lresult._1) match {
      case (ccu.Result.UNKNOWN, ccu.Result. UNKNOWN) => tresult
      case (ccu.Result.UNKNOWN, _) => lresult
      case (_, ccu.Result.UNKNOWN) => tresult
      case (ccu.Result.SAT, ccu.Result.SAT) => tresult
      case (ccu.Result.UNSAT, ccu.Result.UNSAT) => tresult
      case _ => throw new Exception("Different Results!")

    }
  }

  // We automatically calculate unsatCore
  var lastUnsatCore = List() : Seq[Int]


  def unsatCoreAux(problem : CCUSimProblem, timeout : Int) = {
    tsolver.unsatCore(problem, timeout)
  }
}
