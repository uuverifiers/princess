package ccu;

import org.sat4j.core._
import org.sat4j.specs._
import org.sat4j.minisat._
import org.sat4j.tools._

import Timer._

import scala.collection.mutable.{Map => MMap}
import scala.collection.mutable.{Set => MSet}
import scala.collection.mutable.{MutableList => MList}
import scala.collection.mutable.ListBuffer

class Allocator(init : Int) {
  var next = init

  def alloc(count : Int) = {
    val ret = next
    next = next + count
    ret
  }
}

class Table[FUNC](val bits : Int, alloc : Allocator, 
  gt : GateTranslator, solver : ISolver, val terms : List[Int], 
  domains : Map[Int, Set[Int]], functions : List[(FUNC, List[Int], Int)],
  ZEROBIT : Int, ONEBIT : Int) {

  val columns = ListBuffer() : ListBuffer[MMap[Int, List[Int]]]
  var currentColumn = 0

  // Access Table[Column][Row]
  def apply(term : (Int, Int)) = {
    val (col, row) = term
    columns(col)(row)
  }

  //
  //  TERM EQUALITY FUNCTION
  //

  // C[t] == i
  def termEqInt(term : (Int, Int), i : Int) : Int = {
    Timer.measure("termEqInt") {
      var curVal = i

      val lits = 
        (for (t <- this(term)) yield {
          if (curVal % 2 == 1) {
            curVal -= 1
            curVal /= 2
            t
          } else {
            curVal /= 2
            -t
          }
        }).toArray

      val eqBit = alloc.alloc(1)
      gt.and(eqBit, new VecInt(lits))
      eqBit
    }
  }

  // C[t1] == C[t2]
  def termEqTerm(term1 : (Int, Int), term2 : (Int, Int)) : Int = {
    Timer.measure("termEqTerm") {
      val term1Bits = this(term1)
      val term2Bits = this(term2)

      val maxBits = term1Bits.length max term2Bits.length

      val term1BitsPadded = term1Bits.padTo(maxBits, ZEROBIT)
      val term2BitsPadded = term2Bits.padTo(maxBits, ZEROBIT)

      // TODO: Could be optimised (by not doing padding...)
      val eqBits = 
        (for ((t1b, t2b) <- term1BitsPadded zip term2BitsPadded) yield {
          val tmpBit = alloc.alloc(1)
          gt.iff(tmpBit, new VecInt(Array(t1b, t2b)))
          tmpBit
        }).toArray

      val eqBit = alloc.alloc(1)
      gt.and(eqBit, new VecInt(eqBits))
      eqBit
    }
  }

  // C[t1] > C[t2]
  def termGtTerm(term1 : (Int, Int), term2 : (Int, Int)) : Int = {
    Timer.measure("termGtTerm") {
      val (c1, t1) = term1
      val (c2, t2) = term2

      val term1Bits = this(c1, t1)
      val term2Bits = this(c2, t2)
      val maxBits = term1Bits.length max term2Bits.length

      // Make the reversed since we are studying from most significant bit
      val term1BitsPadded = term1Bits.padTo(maxBits, ZEROBIT).reverse
      val term2BitsPadded = term2Bits.padTo(maxBits, ZEROBIT).reverse

      // e_bits[b]: bit (bits-b) of i and j are equal
      var e_bits = List() : List[Int]
      // for (b <- 1 to maxBits) yield {
      for ((t1b, t2b) <- term1BitsPadded zip term2BitsPadded) {

        // term1[bits - b] = term2[bits - b]
        val bitsEq = alloc.alloc(1)
        gt.iff(bitsEq, new VecInt(Array(t1b, t2b)))

        if (e_bits.isEmpty) {
          e_bits = e_bits :+ bitsEq
        } else {
          val prevEq = alloc.alloc(1)
          gt.and(prevEq, e_bits.last, bitsEq)
          e_bits = e_bits :+ prevEq
        }
      }

      var m_bits = List() : List[Int]

      // m_bits[b]: bits [bits..(bits-b)] of i are greater than j
      // for (b <- 1 to bits) {
      for (b <- 0 until maxBits) {
        val bit_gt = alloc.alloc(1)
        gt.and(bit_gt, term1BitsPadded(b), -term2BitsPadded(b))

        if (m_bits.isEmpty) {
          m_bits = m_bits :+ bit_gt
        } else {
          val prev_eq = e_bits(b-1)

          // Option1: All prev bits are eq and this is greater
          val opt1 = alloc.alloc(1)
          gt.and(opt1, prev_eq, bit_gt)

          // Option2: Term1 was already greater than Term2
          val opt2 = m_bits(b-1)

          val m = alloc.alloc(1)
          gt.or(m, new VecInt(Array(opt1, opt2)))
          m_bits = m_bits :+ m
        }
      }
      m_bits.last
    }
  }

  def addInitialColumn(assignments : Map[Int, List[Int]]) {
    val newColumn =
      MMap() ++ (for (t <- terms) yield
        (t, assignments(t))).toMap

    columns += newColumn
  }

  def addDerivedColumn() = {
    Timer.measure("addDerivedColumn") {
      // For all pairs of functions with identical function symbols and 
      // different results,form a 3-tuple of (v_ij, (arg_i, s_i), (arg_j, s_j))
      currentColumn += 1

      val startBit = alloc.alloc(terms.length * bits)

      val newColumn =
        MMap() ++ (List.tabulate(terms.length)(x => {
          (terms(x), List.tabulate(bits)(y => startBit + x*bits + y))
        })).toMap

      columns += newColumn

      val eqBits = Array.tabulate(terms.length, terms.length)( (x, y) => -1)

      // termToIndex
      val tTI = (for (t <- terms) yield (t, terms indexOf t)).toMap

      val V =
        for ((f_i, args_i, s_i) <- functions;
          (f_j, args_j, s_j) <- functions;
          if (f_i == f_j && s_i != s_j)) yield {
          val argBits =
            (for (i <- 0 until args_i.length) yield {
              val t1 = args_i(i) min args_j(i)
              val t2 = args_i(i) max args_j(i)
              if (eqBits(tTI(t1))(tTI(t2)) == -1)
                eqBits(tTI(t1))(tTI(t2)) =
                  termEqTerm((currentColumn-1, args_i(i)),
                    (currentColumn-1,args_j(i)))
              eqBits(tTI(t1))(tTI(t2))
            }).toArray

          // argBit <=> C_p[args_i] = C_p[args_j]
          val argBit = alloc.alloc(1)
          gt.and(argBit, new VecInt(argBits))

          // gtBit <=> C_p[s_i] > C_p[s_j]
          val gtBit = termGtTerm((currentColumn-1, s_i), (currentColumn-1, s_j))

          // vBit <=> args_i = args_j ^ s_i > s_j
          val vBit = alloc.alloc(1)
          gt.and(vBit, argBit, gtBit)

          (vBit, (args_i, s_i), (args_j, s_j))
        }


      for (t <- terms) {
        // --- CASE0: Not a representing term, following a rowless bit ---
        val neqBits = 
          (for (tt <- terms) yield {
            -termEqInt((currentColumn-1, t), tt)
          }).toArray

        val diffBit = alloc.alloc(1)
        gt.and(diffBit, new VecInt(neqBits))

        // Force identity
        val idBit = termEqTerm((currentColumn-1, t), (currentColumn, t))
        solver.addClause(new VecInt(Array(-diffBit, idBit)))

        // --- CASE1: Not a representing term ---

        for (tt <- terms; if t != tt) {
          val eqBit = termEqInt((currentColumn-1, t), tt)
          val asBit = termEqTerm((currentColumn, t), (currentColumn, tt))

          // C_p[t] = tt ==> C_c[t] = C_c[tt]
          solver.addClause(new VecInt(Array(-eqBit, asBit)))
        }

        // --- CASE2: Representing term ---

        // is this term allowed to be identity

        val noVBits =
          (for ((vBit, (args_i, s_i), (args_j, s_j)) <- V) yield {

            // C_p[s_i] = t
            val eqBit = termEqInt((currentColumn-1, s_i), t)
            val ineqBit = alloc.alloc(1)
            gt.not(ineqBit, eqBit)

            val noVBit = alloc.alloc(1)

            // noVBit <=> !V ^ C_p[s_i] != t
            gt.or(noVBit, new VecInt(Array(ineqBit, -vBit)))
            noVBit
          }).toArray


        // vFalseBit <=> No V is true
        val vFalseBit = alloc.alloc(1)
        gt.and(vFalseBit, new VecInt(noVBits))



        // C_c[t] = t
        val eqBit = termEqInt((currentColumn, t), t)

        val identityBit = alloc.alloc(1)
        gt.and(identityBit, vFalseBit, eqBit)

        val funcBits =
          (for ((vBit, (args_i, s_i), (args_j, s_j)) <- V) yield {
            // C_p[s_i] = t
            val prevEqBit = termEqInt((currentColumn - 1, s_i), t)

            // C_c[t] = C_c[s_j]
            val curEqBit = termEqTerm((currentColumn, t), (currentColumn, s_j))

            val fBit = alloc.alloc(1)
            gt.and(fBit, new VecInt(Array(vBit, prevEqBit, curEqBit)))
            fBit
          }).toArray

        val functionalityBit = alloc.alloc(1)
        if (funcBits.length == 0) {
          gt.gateFalse(functionalityBit)
        } else {
          gt.or(functionalityBit, new VecInt(funcBits))
        }

        // C_p[t] = t
        val isRepresentative = termEqInt((currentColumn-1, t), t)

        // C_p[t] = t => (C_c[t] = t v C_c[t] = s) for some functionality t = s
        // not representative OR allowed identity OR derived functionality
        solver.addClause(
          new VecInt(
            Array(-isRepresentative, identityBit, functionalityBit)))
      }
    }
  }

  // TODO: Make sure goal variables are removed at "POP"
  def addGoalConstraint(goals : List[List[(Int, Int)]]) = {
    Timer.measure("addGoalConstraint") {
      val goalBits =
        (for (g <- goals) yield {
          val subGoals = 
            (for ((s, t) <- g) yield {
              termEqTerm((currentColumn, s), (currentColumn, t))
            }).toArray
          val subGoal = alloc.alloc(1)
          gt.and(subGoal, new VecInt(subGoals))
          subGoal
        }).toArray

      solver.addClause(new VecInt(goalBits))
    }
  }

  def addCompletionConstraint() = {
    Timer.measure("addCompletionConstraint") {
      val diff = 
        (for (t <- terms)
        yield (-termEqTerm((currentColumn-1, t), (currentColumn, t)))).toArray
      
      solver.addClause(new VecInt(diff))
    }
  }

  def getCompletionConstraint() = {
    Timer.measure("getCompletionConstraint") {
      val diff = 
        (for (t <- terms)
        yield (-termEqTerm((currentColumn-1, t), (currentColumn, t)))).toArray
      
      val cc = alloc.alloc(1)
      gt.or(cc, new VecInt(diff))
      cc
    }
  }

  def addGoalCompletionConstraint(goals : List[List[(Int, Int)]]) = {
    Timer.measure("addGoalCompletionConstraint") {
      val goalBits =
        (for (g <- goals) yield {
          val subGoals = 
            (for ((s, t) <- g)
            yield termEqTerm((currentColumn, s), (currentColumn, t))).toArray
          
          val subGoal = alloc.alloc(1)
          gt.and(subGoal, new VecInt(subGoals))
          subGoal
        }).toArray

      val goalBit = alloc.alloc(1)
      gt.or(goalBit, new VecInt(goalBits))

      val diff = 
        (for (t <- terms)
        yield (-termEqTerm((currentColumn-1, t), (currentColumn, t)))).toArray
      
      val solverClause = solver.addClause(new VecInt(goalBits ++ diff))
      (solverClause, goalBit)
    }
  }

  def getGoalCompletionConstraint(goals : List[List[(Int, Int)]]) = {
    Timer.measure("getGoalCompletionConstraint") {
      val goalBits =
        (for (g <- goals) yield {
          val subGoals = 
            (for ((s, t) <- g) 
            yield termEqTerm((currentColumn, s), (currentColumn, t))).toArray

          val subGoal = alloc.alloc(1)
          gt.and(subGoal, new VecInt(subGoals))
          subGoal
        }).toArray

      val goalBit = alloc.alloc(1)
      gt.or(goalBit, new VecInt(goalBits))

      val diff = 
        for (t <- terms) 
        yield (-termEqTerm((currentColumn-1, t), (currentColumn, t)))

      val gc = alloc.alloc(1)
      gt.or(gc, new VecInt(goalBits ++ diff))
      (gc, goalBit)
    }
  }
}

class CCUSolver[TERM, FUNC] {

  // SAT4J stuff
  val asd = (Timer.measure("SAT4Jinit") {
    val solverasd = SolverFactory.newDefault()
    val gtasd = new GateTranslator(solverasd)
    

    // TODO: Make real bound?
    val MAXVAR = 1000000;
    solverasd.newVar (MAXVAR);
    (solverasd, gtasd)
  }) : (ISolver, GateTranslator)
  val (solver, gt) = asd

  //
  //  Disequality check
  //

  // List all disequalities, and see which ones can never be united
  // Only send in pairs that are possible, so domains doesn't have to be passed
  // eq shows POSSIBLE equalities
  def disequalityCheck(eq : Array[Array[Int]], 
    functions : List[(FUNC, List[Int], Int)]) = {

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
            // println(">" + s_i + " = " + s_j + ", because of " + 
            // f_i + "(" + args_i + ") = " + f_j + "(" + args_j + ")")
            eq(s_i)(s_j) = 1
            eq(s_j)(s_i) = 1
            changed = true
          }

          // "Transitivity"
          for (i <- 0 until eq.length) {
            for (j <- 0 until eq.length) {
              if (eq(s_i)(i) != 0 && eq(s_j)(j) != 0 && eq(i)(j) == 0) {
                // println(">" + i + " = " + j + ", because of " + s_i + 
                // " = " + i + " and " + s_j + " = " + j)
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

  def tsPairs(assignments : MMap[Int, Int], domains : Map[Int, Set[Int]],
    goals : List[(Int, Int)]) : (Option[MMap[Int, Int]]) = {

    if (goals.isEmpty) {
      Some(assignments)
    } else {
      // Pick out first goal and make larger term LHS
      val (s, t) = goals.head
      val lhs = s max t
      val rhs = s min t

      if (assignments.contains(lhs)) {
        if (assignments(lhs) == rhs) 
          tsPairs(assignments, domains, goals.tail)
        else
          None
      } else {
        val lhsDomain = domains.getOrElse(lhs, Set())
        if (lhsDomain contains rhs) {
          assignments(lhs) = rhs
          tsPairs(assignments, domains, goals.tail)
        } else {
          None
        }
      }
    }
  }

  // Returns an (extended) assignment if one is possible, else None
  def tsSubgoals(
    domains : Map[Int, Set[Int]],
    subGoals : List[List[(Int, Int)]],
    assignment : Map[Int, Int]) : Option[MMap[Int, Int]] = {
    for (pairs <- subGoals) {
      val ass = MMap() : MMap[Int, Int]
      for ((k, v) <- assignment)
        ass(k) = v
      tsPairs(ass, domains, pairs) match {
        case Some(ass) => Some(ass)
        case None => 
      }
    }
    None
  }

  def trivialSolution(domains : Map[Int, Set[Int]], 
    goals : List[List[List[(Int, Int)]]]) : (Option[MMap[Int, Int]]) = {
    var assignment = MMap() : MMap[Int, Int]

    // All problems must be satisfied
    for (subGoals <- goals) {
      tsSubgoals(domains, subGoals, assignment.toMap) match {
        case Some(ass) => assignment = ass
        case None => return None
      }
    }

    Some(assignment)
  }


  //
  // MATH HELPER FUNCTIONS
  //
  
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


  //
  //
  //  PROBLEM PRINTING FUNCTIONS
  //
  //

  def printProblem(terms : List[Int],
    domains : Map[Int, Set[Int]],
    goals : List[List[List[(Int, Int)]]],
    functions : List[List[(FUNC, List[Int], Int)]]) = {
    println("/--PROBLEM--\\")
    for (t <- terms)
      println("| " + t + " = {" + 
        (domains getOrElse (t, Set(t))).mkString(", ") + "}")
    val problemCount = goals.length
    println("| ProblemCount: " + problemCount)
    for (p <- 0 until problemCount) {
     println("| -----------")
      println("| Goals: " + goals(p).mkString(", "))
      println("| Functions: " + functions(p).mkString(", "))
    }
    println("\\----------/")
  }

  //
  //
  //  SOLVER
  //
  //

  def solveaux(
    terms : List[Int],
    domains : Map[Int, Set[Int]],
    goals : List[List[List[(Int, Int)]]],
    functions : List[List[(FUNC, List[Int], Int)]],
    diseq : List[Array[Array[Int]]],
    debug : Boolean) : (Option[Array[Int]], Map[Int, List[Int]]) = {
    Timer.measure("Solveaux") {
      // TODO: optimize such that each table has its own bits
      val bits = binlog(terms.length)
      // Alloc must be shared between tables
      val alloc = new Allocator(1)

      val ZEROBIT = alloc.alloc(1)
      val ONEBIT = alloc.alloc(1)

      // HACK?
      val problemCount = goals.length

      val tables =
        for (p <- 0 until problemCount) yield {
          // Filter terms per table
          def isUsed(term : Int, functions : List[(FUNC, List[Int], Int)], 
            goals : List[List[(Int, Int)]]) : Boolean = {
            for ((_, args, s) <- functions) {
              if (s == term)
                return true
              for (a <- args)
                if (a == term)
                  return true
            }

            for (g <- goals)
              for ((s, t) <- g) 
                if (s == term || t == term)
                  return true

            false
          }

          // TODO: Check arguments agains diseq?
          def matchable(funs : List[(FUNC, List[Int], Int)],
            fun : (FUNC, List[Int], Int)) : Boolean = {
            val (f1, args1, s1) = fun
            for ((f2, args2, s2) <- funs) {
              if (f1 == f2 && s1 != s2) {
                var m = true
                for ((a1, a2) <- args1 zip args2)
                  if (diseq(p)(a1)(a2) == 0)
                    m = false

                if (m)
                  return true
              }
            }
            false
          }

          val filterFunctions = functions(p).filter(x => (matchable(functions(p), x)))
          val filterTerms = terms.filter(x => isUsed(x, filterFunctions, goals(p)))
          val filterDomains = 
            (for ((t, d) <- domains) yield { 
              (t, d.filter(x => filterTerms contains x))
            }).toMap

          // println("Terms before: " + terms)
          // println("\tDomains: " + domains)
          // println("\tFunctions: (" + functions(p).length + "): " + functions(p))
          // println("\tGoals: " + goals(p))
          // println("Terms after: " + filterTerms)
          // println("\tfilterDomains: " + filterDomains)
          // println("\tfilterFunctions: (" + filterFunctions.length + "): " + filterFunctions)
          println("Removed " + (terms.length - filterTerms.length) + " terms")
          println("Removed " + (functions(p).length - filterFunctions.length) + " functions")


          new Table[FUNC](bits, alloc, gt, solver, filterTerms, 
            filterDomains, filterFunctions, ZEROBIT, ONEBIT)
        }
      solver.reset()

      solver.addClause(new VecInt(Array(-ZEROBIT)))
      solver.addClause(new VecInt(Array(ONEBIT)))

      // MAIN SOLVE LOOP
      var cont = true
      var model = None : Option[Array[Int]]


      // Create Initial Column

      def termAssIntAux(i : Int) = {
        var curVal = i

        for (b <- 0 until bits) yield {
          if (curVal % 2 == 1) {
            curVal -= 1
            curVal /= 2
            ONEBIT
          } else {
            curVal /= 2
            ZEROBIT
          }
        }
      }

      def termEqIntAux(bitList : List[Int], i : Int) : Int = {
        Timer.measure("termEqInt") {
          var curVal = i

          val lits =
            (for (b <- bitList) yield {
              if (curVal % 2 == 1) {
                curVal -= 1
                curVal /= 2
                b
              } else {
                curVal /= 2
                -b
              }
            }).toArray

          val eqBit = alloc.alloc(1)
          gt.and(eqBit, new VecInt(lits))
          eqBit
        }
      }

      val assignments =
        (for (t <- terms) yield {
          (t,
            (if (domains(t).size == 1) {
              termAssIntAux(domains(t).toList(0))
            } else {
              val termStartBit = alloc.alloc(bits)
              val termBits = List.tabulate(bits)(x => x + termStartBit)
              val assBits =
                (for (tt <- domains(t); if tt <= t) yield  {
                  val tmpBit = termEqIntAux(termBits, tt)
                  tmpBit
                }).toArray
              solver.addClause(new VecInt(assBits))
              termBits}).toList)}).toMap
        
      for (p <- 0 until problemCount)
        tables(p).addInitialColumn(assignments)

      for (p <- 0 until problemCount) {
        tables(p).addDerivedColumn()
      }

    while (cont) {
      val goalConstraints =
        for (p <- 0 until problemCount) yield
          tables(p).addGoalConstraint(goals(p))

      Timer.measure("isSat") {
      if (solver.isSatisfiable()) {

        def bitToInt(bits : List[Int]) : Int = {
          var curMul = 1
          var curVal = 0
          for (b <-bits) {
            if (solver.model contains b)
              curVal += curMul
            curMul *= 2
          }
          curVal
        }

        model = Option(solver.model)
        // for (p <- 0 until problemCount) {
        //   println("TABLE " + p)
        //   for (t <- tables(p).terms) {
        //     print(t + ">\t")
        //     for (c <- 0 to tables(p).currentColumn) {
        //       val i = bitToInt(tables(p)(c, t))
        //       print("(" + tables(p)(c, t) + " => " + i + ") ")
        //     }
        //     println
        //   }
        // }

        // println(model.mkString(" "))
        cont = false
      } else {
        Timer.measure("completionConstraint") {
        // More info?
        for (gc <- goalConstraints)
          solver.removeConstr(gc)

          val cc = 
            for (p <- 0 until problemCount) yield
              tables(p).addCompletionConstraint()

        if (solver.isSatisfiable()) {
          // Yes, extend necesseray tables
          for (p <- 0 until problemCount) {
              tables(p).addDerivedColumn()
          }
        } else {
          // No
          model = None
          cont = false
        }
        }
      }
      }
    }

      // TODO: Change if differents rows
      Timer.measure("Columns_" + 
        (for (p <- 0 until problemCount) 
        yield tables(p).currentColumn).mkString("[", " ", "]")) { true }

      // println("\tColumns: " + 
      //   (for (p <- 0 until problemCount) 
      //   yield tables(p).currentColumn).mkString("[", " ", "]"))
      // println("\tVariables: " + solver.realNumberOfVariables())
      (model, assignments)
    }
  }

  // Given a list of domains, goals, functions, see if there is a solution to
  // the simultaneous problem.

  def solve_asserted(
    terms : List[TERM],
    domains : Map[TERM, Set[TERM]],
    goals : List[List[List[(TERM, TERM)]]],
    functions : List[List[(FUNC, List[TERM], TERM)]]) 
      : Option[Map[TERM, TERM]] = {
    Timer.measure("Solve") {
      println("\n")
      // TODO: Build up terms automatically

    if (terms.isEmpty || goals.isEmpty) 
      return None

    for (g <- goals)
      if (g.isEmpty)
        return None

      // HACK?
      val problemCount = goals.length

      // Convert to Int representation
      var termToInt = Map() : Map[TERM, Int]
      var intToTerm = Map() : Map[Int, TERM]

      var assigned = 0

      while (assigned < terms.length) {
        for (t <- terms) {
          if (!(termToInt contains t)) {
            var domainAssigned = true 
            for (tt <- (domains getOrElse(t, Set())); if (t != tt)) {
              if (!(termToInt contains tt))
                domainAssigned = false
            }
            if (domainAssigned) {
              termToInt += (t -> assigned)
              intToTerm += (assigned -> t)
              assigned += 1
            }
          }
        }
      }



      val newTerms = terms.map(termToInt)

      var newDomains = Map() : Map[Int, Set[Int]]
      for (t <- terms) {
        val oldDomain = domains getOrElse(t, Set(t))
        newDomains += (termToInt(t) -> oldDomain.map(termToInt))
      }

      val newGoals =
        for (g <- goals)
        yield (for (eqs <- g)
        yield for ((s, t) <- eqs) yield (termToInt(s), termToInt(t)))

      val newFunctions =
        for (funs <- functions)
        yield (for ((f, args, r) <- funs)
        yield (f, args.map(termToInt), termToInt(r)))

        printProblem(newTerms, newDomains, newGoals, newFunctions)


      // --- TRIVIAL SOLUTION CHECK ---
      // Check if any of the goals are trivially satisfied by
      // greedy assignment!
      val ts = trivialSolution(newDomains, newGoals)
      if (ts.isDefined) {
        // Make model
        println("\n\n\n\t\tTRIVIAL SOLUTION FOUND\n\n")
        printProblem(newTerms, newDomains, newGoals, newFunctions)
        println("Solution:")
        println(ts)
        return Some(Map())
      } 

      //
      // --- DISEQUALITY CHECK ---
      // Check if goals are even possible to unify
      // If not we can immeadietly return UNSAT
      val arr = Array.ofDim[Int](newTerms.length, newTerms.length)
      
      for (t <- newTerms) {
        val domain = newDomains getOrElse(t, List(t))
        for (d <- domain) {
          arr(t)(d) = 1
          arr(d)(t) = 1
        }
      }

      // println("arr: \n" + arr.map(x => x.mkString(" ")).mkString("\n"))

      val diseq = (for (p <- 0 until problemCount)
      yield
      {
        val c = Array.ofDim[Int](newTerms.length, newTerms.length)
        for (t <- newTerms; tt <- newTerms) 
          c(t)(tt) = arr(t)(tt)

        val deq = disequalityCheck(c, newFunctions(p))
        deq
      }).toList

      // for (d <- diseq)
      //   println("diseq: \n" + d.map(x => x.mkString(" ")).mkString("\n"))

      // We have p problems, and we are dealing with the simultaneous problem,
      // i.e. every problem must be solvable
      var allGoalPossible = true

      val diseqedGoals = 
      (for (p <- 0 until problemCount) yield {
        // This particular problem consists of subgoals,
        // one of the subgoals must be solvable for the 
        // whole problem to be possible
        (for (gs <- newGoals(p)) yield {
          // A subgoal consists of pairs of terms,
          // all of the must be unifiable for this
          // subgoal to be possible.

          var allUnifiable = true
          for ((s,t) <- gs) {
            if (diseq(p)(s)(t) == 0)
              allUnifiable = false
          }

          (gs, allUnifiable)
        }).filter(x => x._2).map(x => x._1).toList
      }).toList


      if (diseqedGoals contains List()) {
        println("\tDISEQUALITY CHECK DEEMS PROBLEM IMPOSSIBLE")
        return None
      }

      // println("diseqedGoals: " + diseqedGoals)

      // Solve and return UNSAT or SAT  + model
      def bitToInt(bits : List[Int]) : Int = {
        var curMul = 1
        var curVal = 0
        for (b <-bits) {
          if (solver.model contains b)
            curVal += curMul
          curMul *= 2
        }
        curVal
      }


      solveaux(newTerms, newDomains.toMap, 
        diseqedGoals, newFunctions, diseq, false) match {
        case (Some(model), assignments) => {
          var assMap = Map() : Map[TERM, TERM]
          for (t <- newTerms) {
            val iVal = bitToInt(assignments(t))
            // println(t + " := " + iVal)
            assMap += (intToTerm(t) -> intToTerm(iVal))
          }

          Some(assMap)
        }
        case (None, _) =>  {
          // println(termToInt)
          None
        }
      }
    }
  }

  def CC(sets : MSet[Set[TERM]], functions : List[(FUNC, List[TERM], TERM)], 
    assignments : List[(TERM, TERM)] = List()) : Set[Set[TERM]] = {
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

  def checkSAT(
    terms : List[TERM],
    domains : Map[TERM, Set[TERM]], 
    goals : List[List[List[(TERM, TERM)]]],
    functions : List[List[(FUNC, List[TERM], TERM)]],
    solution : Map[TERM, TERM]) : Boolean = {

    val sets = MSet() : MSet[Set[TERM]]
    for (t <- terms)
      sets += Set(t)

    def set(t : TERM) : Set[TERM] = {
      for (s <- sets)
        if (s contains t)
          return s
      throw new Exception("No set contains t?")
    }


    for (p <- 0 until functions.length) {
      // println("\n\nSETS BEFORE:")
      // println(sets.mkString("\n"))
      // println("SOLUTION: " + solution)
      // println("FUNCTIONS: " + functions(p))
      CC(sets, functions(p), solution.toList)
      // println("\n\nSETS AFTER: ")
      // println(sets.mkString("\n"))
      // println(goals(p))
      // Of these subgoals, one must be true
      var anySubGoalTrue = false
      for (subGoal <- goals(p)) {
        var allPairsTrue = true
        for ((s,t) <- subGoal) {
          if (set(s) != set(t)) {
            allPairsTrue = false
          }
        }
        if (allPairsTrue) 
          anySubGoalTrue = true
      }

      if (!anySubGoalTrue) {
        return false
      }
    }

    true
  }

  def checkUNSAT(
    terms : List[TERM],
    domains : Map[TERM, Set[TERM]], 
    goals : List[List[List[(TERM, TERM)]]],
    functions : List[List[(FUNC, List[TERM], TERM)]]) : Boolean = {
    // Enumerate all solutions and do a check sat
    
    if (domains.isEmpty) {
      !(checkSAT(terms, domains, goals, functions, Map()))
    } else {
      // 1. Convert domain to lists of tuples
      var totalSolutions = 1

      val newDomains =
        (for ((k, v) <- domains) yield {
          var tmp = 0
          val asd = (for (vv <- v) yield { 
            tmp += 1 
            (k, vv) 
          }).toList
          totalSolutions *= tmp
          asd
        }).toList

      var checkedSolutions = 0
      // 2. Form all solutions
      def formSolutions(dom : List[List[(TERM, TERM)]], sol : Map[TERM, TERM]) 
          : Option[Map[TERM, TERM]] = {
        if (dom.isEmpty) {
          checkedSolutions += 1
          if (checkedSolutions % 100000 == 0)
            println("Checked " + checkedSolutions + "/" + totalSolutions)
          if (checkSAT(terms, domains, goals, functions, sol.toMap)) {
            Some(sol)
          } else {
            None
          }
        } else {
          for ((k, v) <- dom.head) {
            val isSol = formSolutions(dom.tail, sol + (k -> v))
            if (isSol.isDefined)
              return isSol
          }
          None
        }
      }

      val result = formSolutions(newDomains, Map())
      if (result.isDefined) {
        println("THERE IS SOLUTION: " + result.get)
        false
      } else {
        true
      }
    }
  }

  def solve(
    terms : List[TERM],
    domains : Map[TERM, Set[TERM]],
    goals : List[List[List[(TERM, TERM)]]],
    functions : List[List[(FUNC, List[TERM], TERM)]]) 
      : Option[Map[TERM, TERM]] = {
    solve_asserted(terms, domains, goals, functions) match {
      case Some(sol) =>
        return Some(sol)
        print("Verifying SAT...")
        if (!checkSAT(terms, domains, goals, functions, sol)) {
          println("FALSE SAT!")
          throw new Exception("FalseSATException")
        } else {
          println("OK!")
          Some(sol)
        }
      case None =>
        return None
        print("Verifying UNSAT...")
        if (!checkUNSAT(terms, domains, goals, functions)) {
          println("FALSE UNSAT!")
          throw new Exception("FalseUNSATException")
        } else {
          println("OK!")
          None
        }
    }
  }

}
