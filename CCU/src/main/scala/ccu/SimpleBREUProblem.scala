package ccu;

class SimpleBREUSubProblem[Fun, Term](a : Seq[FlatEquality[Fun, Term]], 
  g : Goal[Fun, Term]) extends BREUSubProblem[Fun, Term] {
  override val assumptions = a
  override val goal = g
}

class SimpleBREUProblem(filename : String)
    extends BREUProblem[Int, Int] {

  println(System.getProperty("user.dir"))
  val lines = scala.io.Source.fromFile(filename).getLines

  println("Read file " + filename)

  if (lines.isEmpty)
    throw new Exception("Empty File!")

  def parseDomains(d : String) = {
    val termData = d.split(" ")
    val map =
      (for (td <- termData) yield {
        val split = td.split(":")
        val term = split(0).toInt
        val domain = split(1).split(",").map(_.toInt).toSet

        term -> domain
      }).toMap
    map
  }


  val count = lines.next.toInt
  val tmpDomains = parseDomains(lines.next)

  val lists = (for (i <- 0 until count) yield {
    val funEqs = lines.next
    val goals = lines.next

    def parseFunEqs(f : String) = {
      val funData = f.split(",")
      val list =
        (for (fd <- funData) yield {
          val split = fd.split(":")
          val fun = split.head.toInt
          val res = split.last.toInt
          val args = split.slice(1, split.size - 1)
          val mapArgs =
            if (args.size == 1 && args(0) == "")
              List()
            else
              args.map(_.toInt).toList
          (fun, mapArgs, res)
        }).toList
      list
    }

    def parseGoals(g : String) = {
      val goalData = g.split(",")
      val list =
        (for (gd <- goalData) yield {
          val split = gd.split(":")
            (for (s <- split) yield {
              val ssplit = s.split('.')
              (ssplit(0).toInt, ssplit(1).toInt)
            }).toList
        }).toList
      list
    }

    println("parsing fun: " + funEqs)
    val fun = parseFunEqs(funEqs)
    println("parsing goal: " + goals)
    val goal = parseGoals(goals)

    (fun, goal)
  })

  val funs = lists.map(x => x._1)
  val goals = lists.map(x => x._2)

  // val instance = Solver.createProblem(tmpDomains, goals, funs)

  override val subProblems = List(new SimpleBREUSubProblem[Int, Int](List(), EquationGoal(0, 0)))
  override val domains = tmpDomains
}
