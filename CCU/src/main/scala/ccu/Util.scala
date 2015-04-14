package ccu;

import scala.collection.mutable.{Set => MSet}
import scala.collection.mutable.{Map => MMap}
import scala.collection.mutable.ListBuffer
import scala.collection.mutable.Queue
import scala.collection.mutable.{HashMap => MHashMap}


class Disequalities(
  val size : Int,
  funEqsAux : Array[CCUEq],
  timeoutChecker : () => Unit) {

  // TODO: Fix!
  val funEqs = funEqsAux.map(_.eq)

  // Stores the actual disequalities 
  // TODO: change to (size*size-1)/2
  var DQarr = Array.ofDim[Int](size * size)

  // Buffer to store change to allow backtracking (old, s, t)
  var changes = ListBuffer() : ListBuffer[(Int, Int, Int)]

  // Maps terms to funEqs with t in argument 
  // | Term -> List(Function, Index, funEq)
  var funArgs = MMap() : MMap[Int, ListBuffer[(Int, Int, Int)]]

  // Maps terms to funEqs with t in result
  // | Term -> List(Function, funEq)
  var funRes = MMap() : MMap[Int, ListBuffer[(Int, Int)]]

  // Fun -> List[functions]
  // Maps function symbols to funEqs with given function symbol 
  // | Function -> List(funEqs)
  var funFuns = MMap() : MMap[Int, ListBuffer[Int]]

  // TODO: diseqCount
  // var diseqCount = 0

  def doprint : Unit = {
    println("DQ:")
    for (i <- 0 until size) {
      for (j <- 0 until size) {
        print(" " + getDQ(i, j))
      }
      println("")
    }
  }

  def pos(i : Int, j : Int) = if (i < j) size*i + j else size*j + i

  def getDQ(i : Int, j : Int) = DQarr(pos(i,j))

  def setDQ(i : Int, j : Int, v : Int) = DQarr(pos(i,j)) = v
 
  def apply(i : Int, j : Int) : Boolean = getDQ(i, j) != 0

  // if (DQ(i)(j) == 0)
  //   diseqCount += 1

  Timer.measure("createProblem.DQ.funArgs/Res/Funs") {
    for (f <- 0 until funEqs.length) {
      val (fun, args, res) = funEqs(f)

      // Argument map
      for (i <- 0 until args.length) {
        if (funArgs contains (args(i)))
          funArgs.get(args(i)).get += ((fun, i, f))
        else
          funArgs += (args(i) -> ListBuffer((fun, i, f)))
      }

      // Result map
      if (funRes contains(res))
        funRes.get(res).get += ((fun, f))
      else
        funRes += (res -> ListBuffer((fun, f)))

      // Function symbol map
      if (funFuns contains(fun))
        funFuns.get(fun).get += f
      else
        funFuns += (fun -> ListBuffer(f))
    }
  }

  def getINEQ() = {
    (for (i <- 0 until size; j <- 0 until size;
      if (i < j); if (0 == getDQ(i, j))) yield
      (i,j))
  }

  def update(i : Int, j : Int, v : Int) = {
    val ii = i min j
    val jj = i max j

    val old = getDQ(ii, jj)
    changes += ((old, ii, jj))

    setDQ(ii, jj, v)
  }

  def unify(i : Int, j : Int) = {
    if (getDQ(i, j) < 1) {
      // diseqCount -= 1
      update(i, j, 1)
    }
  }

  def funify(i : Int, j : Int) = {
    if (getDQ(i ,j) < 2) {
      // if (dq(i,j) < 1)
      //   diseqCount -= 1
      update(i, j, 2)
    }
  }

  def check(pairs : Seq[(Int, Int)]) = {
    if (pairs.isEmpty) {
      true
    } else {
      var equal = true

      val uf = new UnionFind[Int]

      for ((s, t) <- pairs) {
        if (!(uf contains s))
          uf.makeSet(s)
        if (!(uf contains t))
          uf.makeSet(t)

        if (!this(s, t))
          equal = false
        else
          uf.union(s,t)
      }


      if (equal) {
        for (set <- uf.getSets) {
          if (set.size > 2) {
            // println("check(" + pairs + ")")
            // println("\t" + uf)
            // println("\t" + uf.getSets)

            for (s <- set; t <- set; if s < t) {
              if (!this(s,t)) {
                equal = false
                // println("\t\tChecking " + s + " != " + t)
                // throw new Exception("Transitivity CHECK!")
              }
            }
          }
        }
      }
      equal
    }
  }

  def cascadeRemoveDQ(s : Int, t : Int) : Unit = 
  Timer.measure("cascadeRemove") {

    def funUnify(s : Int, t : Int) : Set[(Int, Int)] = {
      val sEq =
        for (i <- 0 until size; if (this(s, i))) yield i
      val tEq =
        for (i <- 0 until size; if (this(t, i))) yield i


      (for (i <- sEq; j <- tEq; if i != j; if !this(i,j)) yield {
        (i min j, i max j)
      }).toSet
    }

    val todo = Queue() : Queue[(Int, Int)]
    val inQueue = Array.ofDim[Boolean](size, size)

    def addTodo(newEq : (Int, Int), fun : Boolean) = {
      val (ss, tt) = newEq
      val s = ss min tt
      val t = ss max tt
      val curdq = getDQ(s, t)

      var queue = true

      if (fun && curdq < 2) {
        funify(s, t)
      } else if (curdq < 1) {
        unify(s, t)
      } else {
        queue = false
      }

      if (queue && !inQueue(s)(t)) {
        inQueue(s)(t) = true
        todo.enqueue((s, t))
      }
    }

    // Add initial todo item
    addTodo((s, t), false)

    while (!todo.isEmpty) {
      timeoutChecker()
      val (s, t) = todo.dequeue
      inQueue(s)(t) = false

      // ASSERT
      if (!this(s, t))
        throw new Exception("Tuple " + ((s,t)) + " in todo not unified!")


      // Functionality
      for ((fun1, i1, eq1) <- funArgs.getOrElse(s, List()); 
        (fun2, i2, eq2) <- funArgs.getOrElse(t, List()); 
        if (fun1 == fun2 && i1 == i2 && eq1 != eq2)) yield {

        val (f_i, args_i, r_i) = funEqs(eq1)
        val (f_j, args_j, r_j) = funEqs(eq2)

        if (check(args_i zip args_j)) {
          addTodo((r_i, r_j), true)
          for (eq <- funUnify(r_i, r_j))
            addTodo(eq, false)
        }
      }



      // Find all s, s.t. s = lhs and add s = rhs
      def transitivity(lhs : Int, rhs : Int) = {
        for ((fun1, eq1) <- funRes getOrElse (lhs, List())) {
          val (_, args_i, _) = funEqs(eq1)

          // Find all matching functions
          for (eq2 <- funFuns getOrElse (fun1, List())) {
            val (_, args_j, s) = funEqs(eq2)

            // s = lhs => s = rhs
            if (check(args_i zip args_j))
              addTodo((s, rhs), false)
          }
        }
      }

      Timer.measure("cascadeRemove.transitivity") {
        transitivity(s, t)
        transitivity(t, s)
      }
    }
  }

  def minimise(goals : Seq[Seq[(Int, Int)]]) = {
    // Go through all disequalities
    // We try to remove disequalities one by one
    // TODO: make it smarter
    this.setBase
    val ineqs = getINEQ()

    for ((s, t) <- ineqs) {
      timeoutChecker()
      this.cascadeRemoveDQ(s, t)

      val sat = this.satisfies(goals)
      if (!sat) {
        this.setBase
      } else {
        this.restore
      }
    }
  }

  def setBase = changes = ListBuffer()

  def restore = {
    for ((old, s, t) <- changes.reverse) {
      // if (old == 0)
      //   diseqCount += 1
      setDQ(s, t, old)
    }

    changes = ListBuffer()
  }

  def satisfies(goals : Seq[Seq[(Int, Int)]]) = {
    var satisfiable = false

    for (subGoal <- goals) {
      var subGoalSat = true

      var allPairsTrue = true
      for ((s,t) <- subGoal) {
        if (!this(s,t))
          allPairsTrue = false

        if (!allPairsTrue)
          subGoalSat = false

      }
      if (subGoalSat)
        satisfiable = true
    }
    satisfiable
  }
}



class UnionFind[D] {
  private val parent = new MHashMap[D, D]
  private val rank   = new MHashMap[D, Int]

  def apply(d : D) : D = {
    val p = parent(d)
    if (p == d) {
      p
    } else {
      val res = apply(p)
      parent.put(d, res)
      res
    }
  }

  def makeSet(d : D) : Unit = {
    parent.put(d, d)
    rank.put(d, 0)
  }

  def union(d : D, e : D) : Unit = {
    val dp = apply(d)
    val ep = apply(e)
    
    if (dp != ep) {
      val dr = rank(dp)
      val er = rank(ep)
      if (dr < er) {
        parent.put(dp, ep)
      } else if (dr > er) {
        parent.put(ep, dp)
      } else {
        parent.put(ep, dp)
        rank.put(dp, dr + 1)
      }
    }
  }

  def getSets = parent.groupBy(_._2).mapValues(_.map(_._1)).values

  def contains(d : D) : Boolean = {
    parent contains d
  }

  override def toString : String = parent.toString
}

class Util (timeoutChecker : () => Unit) {
  // Calculating log_2 (b)
  // Used for cacluating number of bits needed
  def binlog(b : Int) : Int = {
    Timer.measure("binlog") {
      var bits = b
      var log = 0
      if ((bits & 0xffff0000) != 0) {
        bits >>>= 16
        log = 16
      }
      
      if (bits >= 256) {
        bits >>>= 8
        log += 8
      }
      if (bits >= 16) {
        bits >>>= 4
        log += 4
      }
      
      if (bits >= 4) {
        bits >>>= 2
        log += 2
      }

      // TODO: Add 1 for luck!
      // Add one if we have an even power of 2
      // if ((b & (b -1)) == 0)
      return log + ( bits >>> 1 ) + 1
      // else 
        // return log + (bits >>> 1)
    }
  }

  def CCunionFind(
    terms : Seq[Int],
    equations : Seq[CCUEq],
    assignments : Seq[(Int, Int)] = List()) 
  : UnionFind[Int]= {

    val functions = equations.map(_.eq)
    val uf = new UnionFind[Int]

    for (t <- terms)
      uf.makeSet(t)

    // First merge assigned terms
    for ((s, t) <- assignments)
      uf.union(s, t)

    // Fix-point calculation
    var changed = true
    while (changed) {
      changed = false
      // All pairs of functions, if args_i = args_j, merge s_i with s_j
      for ((f_i, args_i, s_i) <- functions;
        (f_j, args_j, s_j) <- functions;
        if (f_i == f_j && uf(s_i) != uf(s_j))) {
        var argsEquals = true
        for (i <- 0 until args_i.length) {
          if (uf(args_i(i)) != uf(args_j(i)))
            argsEquals = false
        }
        if (argsEquals) {
          uf.union(s_i, s_j)
          changed = true
        }
      }
    }

    uf
  }

  def dummyTimeout() = ()

  def solveFile(fname : String) = {
    // val Solver = new TableSolver[Int,Int](dummyTimeout, 1000000)

    // val lines = scala.io.Source.fromFile(fname).getLines
    // println("Read file " + fname)
    // if (lines.isEmpty)
    //   throw new Exception("Empty File!")

    // def parseDomains(d : String) = {
    //   val termData = d.split(" ")
    //   val map =
    //     (for (td <- termData) yield {
    //       val split = td.split(":")
    //       val term = split(0).toInt
    //       val domain = split(1).split(",").map(_.toInt).toSet

    //       term -> domain
    //     }).toMap
    //   map
    // }


    // val count = lines.next.toInt
    // val domains = parseDomains(lines.next)

    // val lists = (for (i <- 0 until count) yield {
    //   val funEqs = lines.next
    //   val goals = lines.next

    //   def parseFunEqs(f : String) = {
    //     val funData = f.split(",")
    //     val list =
    //       (for (fd <- funData) yield {
    //         val split = fd.split(":")
    //         val fun = split.head.toInt
    //         val res = split.last.toInt
    //         val args = split.slice(1, split.size - 1)
    //         val mapArgs = 
    //           if (args.size == 1 && args(0) == "")
    //             List()
    //           else
    //             args.map(_.toInt).toList
    //         (fun, mapArgs, res)
    //       }).toList
    //     list
    //   }

    //   def parseGoals(g : String) = {
    //     val goalData = g.split(",")
    //     val list =
    //       (for (gd <- goalData) yield {
    //         val split = gd.split(":")
    //           (for (s <- split) yield {
    //             val ssplit = s.split('.')
    //             (ssplit(0).toInt, ssplit(1).toInt)
    //           }).toList
    //       }).toList
    //     list
    //   }

    //   println("parsing fun: " + funEqs)
    //   val fun = parseFunEqs(funEqs)
    //   println("parsing goal: " + goals)
    //   val goal = parseGoals(goals)

    //   (fun, goal)
    // })

    // val funs = lists.map(x => x._1)
    // val goals = lists.map(x => x._2)

    // TODO: Fix output
    // Solver.debug = true
    // val instance = Solver.createProblem(domains, goals, funs)
    // println(instance)
    // println("Trying to solve...")
    // println("RESULT: " + instance.solve)
    // val a = 10/0
  }
}




