package ccu;

import scala.io.Source
import scala.collection.mutable.Map

object CCURun {
  //
  // BEGIN OF FILE READING FUNCTIONS
  //
  
  // Problem = (Terms, Domains, Goals, Functions)
  type Problem = (List[Int], Map[Int,Set[Int]], List[List[(Int, Int)]], List[(Int, List[Int], Int)])

  def parsegoals(line : String) = {
    val goals = line.split("-")
      (for (g <- goals) yield
      {
        val s = g.split(" ")
        (s(0).toInt, s(1).toInt)
      }).toList
  }

  def parsefunctions(line : String) : List[(Int, List[Int], Int)] = {
    if (line == "")
      return List()
    val functions = line.split("-")
      (for (f <- functions) yield
      {
        val s = f.split(" ").toList.map(x => x.toInt)
        (s(0).toInt, s.drop(2), s(1).toInt)
      }).toList
  }

  def parseFile(Filename : String) = {
    val lines = Source.fromFile(Filename).getLines()
    var problems = List() : List[(String, Problem)]

    while (lines.hasNext) {
      val Title = lines.next
      val Constants = lines.next.toInt
      val Variables = lines.next.toInt
      val goals = List(parsegoals(lines.next))
      val functions = parsefunctions(lines.next)

      var domains = scala.collection.mutable.Map() : scala.collection.mutable.Map[Int, Set[Int]]
      for (c <- 0 until Constants)
        domains(c) = Set() : Set[Int]
      for (v <- Constants until (Constants + Variables))
        domains(v) = (0 to v).toSet

      problems ::= ((Title, ((0 until (Constants + Variables)).toList, domains, goals, functions)))
    }
    problems.reverse
  }

  //
  // END OF FILE READING FUNCTIONS
  //


  def main(args: Array[String]) {
    val ccusolver = new CCUSolver[Int, Int]()

    for (f <- args) {
      println("FILE: " + f)
      for ((title, p) <- parseFile(f)) {
        val (t, d, g, f) = p
        val result = ccusolver.solve(t, d, g, f)

        result match {
          case Some(model) => {
            println(title + " = SAT")
            for ((k,v) <- model)
              println(k + " := " + v)
          }
          case None => {
            println(title + " = UNSAT")
          }
        }
      }
    }
  }
}
