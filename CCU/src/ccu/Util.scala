package ccu;

import scala.collection.mutable.{Set => MSet}
import scala.collection.mutable.ListBuffer
import scala.annotation.tailrec


class Disequalities[FUNC](
  initialDiseqs : Array[Array[Int]],
  functions : List[(FUNC, List[Int], Int)]) {

  var DQ = Array() : Array[Array[Int]]
  var changes = ListBuffer() : ListBuffer[(Int, Int, Int)]
  var relMap = Map() : Map[(Int, Int), List[((FUNC, List[Int], Int), (FUNC, List[Int], Int))]]
  var goalMap = Map() : Map[Int, List[((FUNC, List[Int], Int), (FUNC, List[Int], Int))]]


  Timer.measure("DISEQ.init") {
    Timer.measure("DISEQ.DQ") {
      DQ = Array.ofDim[Int](initialDiseqs.size, initialDiseqs.size)
      for (i <- 0 until DQ.size; j <- 0 until DQ.size)
        DQ(i)(j) = initialDiseqs(i)(j)
    }


    Timer.measure("DISEQ.relMap") {
      // Build up a map from term-tuples to function-pairs that are relevant
      relMap =
        (for (i <- 0 until DQ.size; j <- 0 until DQ.size;
          if (i < j)) yield {
          ((i, j),
            (for (f1 <- 0 until functions.length; f2 <- 0 until functions.length;
              if f1 < f2)
            yield (functions(f1), functions(f2))).filter(x => {
              val ((fun1, args1, res1), (fun2, args2, res2)) = x
              val zipArgs = args1 zip args2
              (fun1 == fun2) && ((zipArgs contains (i,j)) || (zipArgs contains (j,i)))
            }).toList)
        }).toMap
    }

    Timer.measure("DISEQ.goalMap") {
      goalMap =
        (for (i <- 0 until DQ.size)
        yield {
          (i,
            (for (f1 <- 0 until functions.length; f2 <- 0 until functions.length)
            yield (functions(f1), functions(f2))).filter(x => {
              val ((fun1, args1, res1), (fun2, args2, res2)) = x
              fun1 == fun2 && res1 == i && res2 != i
            }).toList)
        }).toMap
    }
  }

  //
  // GET/SET
  //
  def apply(i : Int, j : Int) : Boolean = {
    if (i < j)
      DQ(i)(j) != 0
    else
      DQ(j)(i) != 0
  }

  def dq(i : Int, j : Int) : Int = {
    if (i < j)
      DQ(i)(j)
    else
      DQ(j)(i)
  }



  def getDQ() = {
    val copy = Array.ofDim[Int](DQ.size, DQ.size)
    for (i <- 0 until DQ.size; j <- 0 until DQ.size)
      copy(i)(j) = (if (this(i, j)) 1 else 0)

    copy
  }

  def getINEQ() = {
    (for (i <- 0 until DQ.length; j <- 0 until DQ.length;
      if (i < j); if (0 == DQ(i)(j))) yield
      (i,j)).toList
  }

  def getChanges() = changes

  def unify(i : Int, j : Int) = {
    if (dq(i, j) < 1) {
      val old = DQ(i min j)(i max j)
      changes += ((old, (i min j), (i max j)))
      if (i < j)
        DQ(i)(j) = 1
      else
        DQ(j)(i) = 1
    }
  }

  def funify(i : Int, j : Int) = {
    if (dq(i ,j) < 2) {
      val old = DQ(i min j)(i max j)
      changes += ((old, (i min j), (i max j)))
      if (i < j)
        DQ(i)(j) = 2
      else
        DQ(j)(i) = 2
    }
  }

  def cascadeRemoveDQ(s : Int, t : Int) : Unit = {

    def funUnify(s : Int, t : Int) : Set[(Int, Int)] = {
      Timer.measure("CASC.funUnify") {
        val sEq =
          for (i <- 0 until DQ.length; if (this(s, i))) yield i
        val tEq =
          for (i <- 0 until DQ.length; if (this(t, i))) yield i

        // println("sEq: " + sEq)
        // println("tEq: " + tEq)

        (for (i <- sEq; j <- tEq; if i != j; if !this(i,j)) yield {
          // println(((i min j, i max j)) + " because of " + ((s, t)) +
          //   " was removed and " + ((s, i)) + " and " + ((t, j)))
          (i min j, i max j)
        }).toSet
      }
    }

    val done = MSet() : MSet[(Int, Int)]
    var todo = MSet((s, t))

    while (!todo.isEmpty) {
      val next = todo.head
      todo -= next

      val (s,t) = next
      if (s != t && !(done contains next)) {
        done += next

        // Remove (s != t)
        unify(s, t)

        Timer.measure("CASC.Functionality") {
          // Functionality
          for (((f_i, args_i, s_i), (f_j, args_j, s_j)) <- relMap((s,t))) {
            var equal = true
            for (i <- 0 until args_i.length)
              if (!this(args_i(i), args_j(i)))
                equal = false

            if (equal) {
              if (2 != dq(s_i, s_j)) {
                funify(s_i, s_j)
                val newEq = (s_i min s_j, s_i max s_j)
                if (!(done  contains newEq))
                  todo += newEq
                for (eq <- funUnify(s_i, s_j); if (!(done contains eq)))
                  todo += eq
              }

            }
          }
        }

        Timer.measure("CASC.goalMap(s)") {
          for (((f_i, args_i, s_i), (f_j, args_j, s_j)) <- goalMap(s)) {
            var equal = true
            for (k <- 0 until args_i.length)
              if (!this(args_i(k), args_j(k)))
                equal = false
            if (equal)
              // We know that s_i = s
              for (i <- 0 until DQ.length) {
                if (!this(t, i) && this(i, s_j) && !(done contains (t, i))) {
                  todo += (((t min i, t max i)))
                }
              }
          }
        }

        Timer.measure("CASC.goalMap(t)") {
          for (((f_i, args_i, s_i), (f_j, args_j, s_j)) <- goalMap(t)) {
            var equal = true
            for (k <- 0 until args_i.length)
              if (!this(args_i(k), args_j(k)))
                equal = false
            if (equal)
              // We know that s_i = s
              for (i <- 0 until DQ.length) {
                if (!this(s, i) && this(i, s_j) && !(done contains (s, i))) {
                  todo += (((s min i, s max i)))
                }
              }
          }
        }
      }
      
    }
  }


  def equalTo(DQ2 : Disequalities[FUNC]) : Boolean = {
    if (DQ.size != DQ2.DQ.size)
      return false

    for (i <- 0 until DQ.size; j <- 0 until DQ.size; if i<=j)
      if (this(i, j) != DQ2(i, j))
        return false
    true
  }

  def setBase() = {
    changes = ListBuffer()
  }

  def restore() = {
    for ((old, s, t) <- changes.reverse)
      DQ(s)(t) = old
    changes = ListBuffer()
  }

  def doprint() : Unit = {

    println(DQ)
    // for (i <- 0 until DQ.size) {
    //   for (j <- 0 until DQ.size) {
    //     print(" " + (DQ(i)(j)))
    //   }
    //   println
    // }
    // println(DQ.map(x => x.mkString(" ")).mkString("\n"));
  }

  // "Congruence Closure"
  // Returns list of disequalities removed
  def pruneINEQ() : List[(Int, Int)] = {
    var changed = true

    while (changed) {
      changed = false

      // Functionality & Transitivity
      for ((f_i, args_i, s_i) <- functions;
        (f_j, args_j, s_j) <- functions;
        if (f_i == f_j && s_i != s_j))
      {
        var equal = true
        for (i <- 0 until args_i.length)
          if (!this(args_i(i), args_j(i)))
            equal = false

        // Functionality
        if (equal) {
          if (!this(s_i, s_j)) {
            // println(((s_i, s_j)) + " because of " + ((f_i, args_i, s_i)) +
            //   " and " + ((f_j, args_j, s_j)) + " (FUNC)")
            println("FUNIFY(" + s_i + ", " + s_j + ")")
            funify(s_i, s_j)
            changed = true
          }

          // "Transitivity"
          for (i <- 0 until DQ.length) {
            for (j <- 0 until DQ.length) {
              if (this(s_i, i) && this(s_j, j) && !this(i, j)) {
                // println(((s_i, s_j)) + " because of " + ((f_i, args_i, s_i)) +
                //   " and " + ((f_j, args_j, s_j)) + " and " + ((s_i, i)))
                println("UNIFY(" + i + ", " + j + ")")
                unify(i, j)
                changed = true
              }
            }
          }
        }
      }
    }

    changes.map(x => {
      val (a,b,c) = x
      (b, c)
    }).toList
  }

  def satisfies(goals : List[List[(Int, Int)]]) = {
    var satisfiable = false

    for (subGoal <- goals) {
      var subGoalSat = true

      var allPairsTrue = true
      for ((s,t) <- subGoal) {
        if (!this(s,t)) {
          allPairsTrue = false
        }

        if (!allPairsTrue)
          subGoalSat = false
      }
      if (subGoalSat)
        satisfiable = true
    }
    satisfiable
  }
}

class Util[TERM, FUNC] {
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

  def CC[FUNC, TERM](
    sets : MSet[Set[TERM]], 
    functions : List[(FUNC, List[TERM], TERM)],
    assignments : List[(TERM, TERM)] = List()) 
      : Set[Set[TERM]] = {
    def rep(t : TERM) : TERM = {
      for (s <- sets)
        if (s contains t)
          return s.minBy(_.toString)
      throw new Exception("No set contains t?")
    }

    def set(t : TERM) : Set[TERM] = {
      for (s <- sets)
        if (s contains t)
          return s
      throw new Exception("No set contains t?")
    }

    def mergeSets(t1 : TERM, t2 : TERM) : Unit = {
      val set1 = set(t1)
      val set2 = set(t2)

      val newset = set1 ++ set2
      sets -= set1
      sets -= set2
      sets += newset
    }

    // First merge assigned terms
    for ((s, t) <- assignments) {
      mergeSets(s, t)
    }

    // Fix-point calculation
    var changed = true
    while (changed) {
      changed = false
      // All pairs of functions, if args_i = args_j, merge s_i with s_j
      for ((f_i, args_i, s_i) <- functions;
        (f_j, args_j, s_j) <- functions;
        if (f_i == f_j && set(s_i) != set(s_j))) {
        var argsEquals = true
        for (i <- 0 until args_i.length) {

          if (set(args_i(i)) != set(args_j(i)))
            argsEquals = false
        }
        if (argsEquals) {
          mergeSets(s_i, s_j)
          changed = true
        }
      }
    }

    sets.toSet
  }


  //
  //  Disequality check
  //

  // List all disequalities, and see which ones can never be united
  // Only send in pairs that are possible, so domains doesn't have to be passed
  // eq shows POSSIBLE equalities
  def disequalityCheck(eq : Array[Array[Int]],
    functions : List[(FUNC, List[Int], Int)]) = {
    Timer.measure("DICC") {

      var changed = true
      while (changed) {
        changed = false

        // Functionality & Transitivity
        for ((f_i, args_i, s_i) <- functions;
          (f_j, args_j, s_j) <- functions;
          if (f_i == f_j && s_i != s_j))
        {
          var equal = true
          for (i <- 0 until args_i.length) {
            if (eq(args_i(i) min args_j(i))(args_i(i) max args_j(i)) == 0) {
              equal = false
            }
          }

          // Functionality
          if (equal) {
            if (eq(s_i min s_j)(s_i max s_j) == 0) {
              println(">" + s_i + " = " + s_j + ", because of " +
              f_i + "(" + args_i + ") = " + f_j + "(" + args_j + ")")
              eq(s_i)(s_j) = 1
              eq(s_j)(s_i) = 1
              changed = true
            }

            // "Transitivity"
            for (i <- 0 until eq.length) {
              for (j <- 0 until eq.length) {
                if (eq(s_i)(i) != 0 && eq(s_j)(j) != 0 && eq(i)(j) == 0) {
                  println(">" + i + " = " + j + ", because of " + s_i +
                  " = " + i + " and " + s_j + " = " + j)
                  eq(i)(j) = 1
                  eq(j)(i) = 1
                  changed = true
                }
              }
            }
          }
        }

      }
      eq
    }
  }


}
