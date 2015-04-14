package ccu;

import java.io.FileOutputStream
import java.io.ObjectOutputStream
import java.io.File


class CCUInstance[Term, Fun](
  id : Int, 
  solver : CCUSolver,
  problem : CCUSimProblem,
  termMap : Map[Term, Int]) {

  // var origTerms = List() : Seq[Term]
  // var origDomains = Map() : Map[Term, Set[Term]]
  // var origFunctions = List() : Seq[Seq[(Fun, Seq[Term], Term)]]
  // var origGoals = List() : Seq[Seq[Seq[(Term, Term)]]]

  var model = None : Option[Map[Term, Term]]


  def confirmActive = {
    if (solver.curId != id)
      throw new Exception("New instance has been created by solver")
  }

  def solve : Result.Result = {
    confirmActive
    val retval = 
      try {
        solver.solve(problem, true)
      } catch {
        case to : org.sat4j.specs.TimeoutException => {
          ccu.Result.UNKNOWN
        }
      }
    retval
  }

  def solveAsserted = {
    confirmActive
    solver.solve(problem, true)
  }

  def notUnifiable(prob : Int, s : Term, t : Term) : Boolean = {
    confirmActive
    // TODO: Does this work?
    (for (i <- termMap get s;
          j <- termMap get t)
     yield (!problem(prob).DQ(i, j))) getOrElse (s != t)

  }

  def unsatCore(timeout : Int) = {
    confirmActive
    val core =
      try {
        solver.unsatCore(problem, timeout)
      } catch {
        case to : org.sat4j.specs.TimeoutException => {
          (0 until problem.size)
        }
      }
    core
  }

  def print = println("SOMETHING SHOULD BE PRINTED")
     // solver.problem.print

  // TODO: SERIALIZE?
  def output(filename : String) = {
    // import java.io._
    // val writer = new PrintWriter(new File("test.txt"))
    // var output = ""
    // output += subProblems.length + "\n"
    // output += domains.map(x => { val (k,v) = x; k + ":" + v.mkString(",") }).mkString(" ") + "\n"
    // output += subProblems.mkString("\n")
    // writer.write(output)
    // writer.close()

    val file = new File(filename)
    val fos = new FileOutputStream(file)
    val oos = new ObjectOutputStream(fos)
    
    oos.writeObject(problem)
    oos.close

    println(filename)
    println(fos)
    println(oos)
    println("Printed to: " + filename)
  }
}
