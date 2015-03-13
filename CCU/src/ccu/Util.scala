package ccu;

import scala.collection.mutable.{Set => MSet}
import scala.collection.mutable.{Map => MMap}
import scala.collection.mutable.ListBuffer
import scala.collection.mutable.Queue
import scala.collection.mutable.{HashMap => MHashMap}


class Disequalities(
  val size : Int,
  functions : Seq[(Int, Seq[Int], Int)],
  timeoutChecker : () => Unit) {

  var DQarr = Array.ofDim[Int](size * size)
  var changes = ListBuffer() : ListBuffer[(Int, Int, Int)]
  var relMap = MMap() : MMap[(Int, Int), List[(Int, Int)]]
  var goalMap = MMap() : MMap[Int, List[(Int, Int)]]

  // var diseqCount = 0

  def doprint : Unit = {
    println("DQ:")
    for (i <- 0 until size) {
      for (j <- 0 until size) {
        print(" " + gDQ(i, j))
      }
      println("")
    }
  }

  def gDQ(i : Int, j : Int) = {
    val pos =
      if (i < j)
        size*i + j
      else
        size*j + i

    DQarr(pos)
  }

  def sDQ(i : Int, j : Int, v : Int) = {
    val pos = 
      if (i < j)
        size*i + j
      else
        size*j + i

    DQarr(pos) = v
  }



  // if (DQ(i)(j) == 0)
  //   diseqCount += 1

  // println("Building DQ")
  // println("\tfuncount: " + functions.length)
  // println("\tsize: " + size)

  goalMap = MMap()
  relMap = MMap()

  // Build up a map from term-tuples to function-pairs that are relevant
  for (f1 <- 0 until functions.length; f2 <- 0 until functions.length;
    if f1 < f2) {
    val (fun1, args1, res1) = functions(f1)
    val (fun2, args2, res2) = functions(f2)
    if (fun1 == fun2 && res1 != res2) {
      // RelMap
      for (i <- 0 until args1.length) {
        val s = args1(i) min args2(i)
        val t = args1(i) max args2(i)

        val newList = (f1, f2) ::
        (relMap.getOrElse((s, t), List()))
        relMap += ((s, t)) -> newList
      }

      // GoalMap
      Timer.measure("createProblem.DQ.goalMap2") {
        val oldRes1 = goalMap.getOrElse(res1, List() : List[(Int, Int)])
        val oldRes2 = goalMap.getOrElse(res2, List() : List[(Int, Int)])

        goalMap += (res1 -> ((f1, f2) :: oldRes1))
        goalMap += (res2 -> ((f2, f1) :: oldRes2))
      }
    }
  }


  //
  // GET/SET
  //
  def apply(i : Int, j : Int) : Boolean = {
    if (i < j)
      gDQ(i, j) != 0
    else
      gDQ(j, i) != 0
  }

  def getINEQ() = {
    (for (i <- 0 until size; j <- 0 until size;
      if (i < j); if (0 == gDQ(i, j))) yield
      (i,j))
  }

  def update(i : Int, j : Int, v : Int) = {
    val ii = i min j
    val jj = i max j

    val old = gDQ(ii, jj)
    changes += ((old, ii, jj))

    sDQ(ii, jj, v)
  }

  def unify(i : Int, j : Int) = {
    if (gDQ(i, j) < 1) {
      // diseqCount -= 1
      update(i, j, 1)
    }
  }

  def funify(i : Int, j : Int) = {
    if (gDQ(i ,j) < 2) {
      // if (dq(i,j) < 1)
      //   diseqCount -= 1
      update(i, j, 2)
    }
  }

  def cascadeRemoveDQ(s : Int, t : Int) : Unit = {

    def funUnify(s : Int, t : Int) : Set[(Int, Int)] = {
      val sEq =
        for (i <- 0 until size; if (this(s, i))) yield i
      val tEq =
        for (i <- 0 until size; if (this(t, i))) yield i


      (for (i <- sEq; j <- tEq; if i != j; if !this(i,j)) yield {
        // println(((i min j, i max j)) + " because of " + ((s, t)) +
        //   " was removed and " + ((s, i)) + " and " + ((t, j)))
        (i min j, i max j)
      }).toSet
    }

    val todo = Queue() : Queue[(Int, Int)]
    val inQueue = Array.ofDim[Boolean](size, size)

    def addTodo(newEq : (Int, Int), fun : Boolean) = {
      val (ss, tt) = newEq
      val s = ss min tt
      val t = ss max tt
      val curdq = gDQ(s, t)

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

    // DISEQ COUNT?
    while (!todo.isEmpty) {
      timeoutChecker()
      val (s, t) = todo.dequeue
      inQueue(s)(t) = false

      // ASSERT
      if (!this(s, t))
        throw new Exception("Tuple " + ((s,t)) + " in todo not unified!")


      // Functionality
      // println("FUNC" + ((s, t)))
      // println("\t" + relMap.getOrElse((s,t), List()))
      // println("\n\t\trelMap: " + relMap)
      for ((f1, f2) <- relMap.getOrElse((s,t), List())) {
        val (f_i, args_i, s_i) = functions(f1)
        val (f_j, args_j, s_j) = functions(f2)
        // println("\t" + (f_i, args_i, s_i) + " and " + (f_j, args_j, s_j))

        var equal = true

        for (i <- 0 until args_i.length)
          if (!this(args_i(i), args_j(i)))
            equal = false

        if (equal) {
          addTodo((s_i, s_j), true)

          for (eq <- funUnify(s_i, s_j))
            addTodo(eq, false)
        }
      }

      for ((f1, f2) <- goalMap getOrElse (s, List())) {
        val (f_i, args_i, s_i) = functions(f1)
        val (f_j, args_j, s_j) = functions(f2)

        var equal = true
        for (k <- 0 until args_i.length)
          if (!this(args_i(k), args_j(k)))
            equal = false

        if (equal) {
          // We know that s_i = s
          for (i <- 0 until size; if (i != s && i != t)) {
            if (this(i, s_j))
              addTodo((t, i), false)
          }
        }
      }

      for ((f1, f2) <- goalMap getOrElse (t, List())) {
        val (f_i, args_i, s_i) = functions(f1)
        val (f_j, args_j, s_j) = functions(f2)

        var equal = true
        for (k <- 0 until args_i.length)
          if (!this(args_i(k), args_j(k)))
            equal = false

        if (equal) {
          // We know that s_i = s
          for (i <- 0 until size; if (i != s && i != t)) {
            if (this(i, s_j))
              addTodo((s, i), false)
          }
        }
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

  def equalTo(DQ2 : Disequalities) : Boolean = {
    if (size != DQ2.size)
      return false

    for (i <- 0 until size; j <- 0 until size; if i<=j)
      if (this(i, j) != DQ2(i, j))
        return false
    true
  }

  def setBase = {
    changes = ListBuffer()
  }

  def restore = {
    for ((old, s, t) <- changes.reverse) {
      // if (old == 0)
      //   diseqCount += 1
      sDQ(s, t, old)
    }

    changes = ListBuffer()
  }

  // "Congruence Closure"
  // Returns list of disequalities removed

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

  override def toString : String = parent.toString
}

class Util[TERM, FUNC] (timeoutChecker : () => Unit) {
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
      // Actually only needed for 2, 4, 8, 16, 32 ...
      return log + ( bits >>> 1 ) + 1
    }
  }

  def CCunionFind[FUNC, TERM](
    terms : Seq[TERM],
    functions : Seq[(FUNC, Seq[TERM], TERM)],
    assignments : Seq[(TERM, TERM)] = List()) 
  : UnionFind[TERM]= {

    val uf = new UnionFind[TERM]

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
}


