package ccu;

import org.sat4j.core._
import org.sat4j.specs._
import org.sat4j.minisat._
import org.sat4j.tools._

import scala.collection.mutable.Map

class Table(BITS : Int, ROWS : Int) {

  val asd = 12
}

class CCUSolver[TERM, FUNC] {

  // SAT4J stuff
  val solver = SolverFactory.newDefault()
  val gt = new GateTranslator(solver)

  // TODO: Make real bound?
  val MAXVAR = 1000000;

  // Problem = (Terms, Domains, Goals, Functions)
  type Problem = (List[TERM], Map[TERM, Set[TERM]], List[List[(TERM, TERM)]], List[(FUNC, List[TERM], TERM)])

  // 
  // MATH HELPER FUNCTIONS
  //
  
  // Calculating log_2 (b)
  // Used for cacluating number of bits needed
  def binlog(b : Int) : Int = {
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



  //
  // SOLVER FUNCTIONS
  //
  def solveaux(terms : List[Int], domains : Map[Int, Set[Int]], goals : List[List[(Int, Int)]], functions : List[(FUNC, List[Int], Int)], debug : Boolean) : (Option[Array[Int]], Map[(Int, Int), Int]) = {

    var slackvars = scala.collection.mutable.MutableList() : scala.collection.mutable.MutableList[Int]
    var assignments = Map() : Map[(Int, Int), Int]
    val BITS = binlog(terms.length)


    //
    // DEBUG FUNCTIONS
    //

    def printModel(Model : Array[Int], EndColumn : Int)(implicit BITS : Int) = {
      def iT(Column : Int, Row : Int) : Int = {
        val startBit = T(Column, Row)
        var multiplier = 1
        var n = 0
        for (i <- (0 until BITS)) {
          if (Model contains (startBit + i))
            n +=  multiplier
          else if (Model contains -(startBit + i))
            n += 0
          else
            return -1
          multiplier *= 2
        }
        n
      }

      println("Terms:")
      for (t <-terms) {
        print(t + "> ")
        for (i <- 0 to EndColumn)
          print(iT(i, t) + " ")
        println()
      }

      println("No of bits: " + BITS)
    }

    //
    // UTILITY FUNCTIONS
    //

    // Access Table[Column][Row]
    def T(Column : Int, Row : Int) : Int = 1 + Column*(terms.length)*BITS + slackvars.take(Column).sum + Row*BITS

    // allocate a new variable
    def allocate(Column : Int) : Int = {
      val newBit = T(Column + 1, 0)
      slackvars(Column) += 1
      newBit
    }


    //
    //  TERM EQUALITY FUNCTION
    // 

    // C[t] == i
    def TermEqInt(term : (Int, Int), i : Int, alloc : Int) : Int = {
      val (c, t) = term

      // TODO: Optimize
      var lits = List() : List[Int]
      var curBit = T(c, t)
      var curVal = i
      while (curVal > 0) {
        if (curVal % 2 == 1) {
          lits ::= curBit
          curVal -= 1
        } else {
          lits ::= -curBit
        }
        curBit += 1
        curVal /= 2
      }

      while (lits.length < BITS) {
        lits ::= -curBit
        curBit += 1
      }

      val prevBit = allocate(alloc)
      gt.and(prevBit, new VecInt(lits.toArray))
      prevBit
    }

    // C[t1] == C[t2]
    def TermEqTerm(Term1 : (Int, Int), Term2 : (Int, Int), alloc : Int) : Int = {
      val (c1, t1) = Term1
      val (c2, t2) = Term2
      val iBit = T(c1, t1)
      val jBit = T(c2, t2)

      val eqBits = 
        for (b  <- 0 until BITS) yield {
          val tmpBit = allocate(alloc)
          gt.iff(tmpBit, new VecInt(List(iBit + b, jBit + b).toArray))
          tmpBit
        }

      val eqBit = allocate(alloc)
      gt.and(eqBit, new VecInt(eqBits.toArray))
      eqBit
    }

    // C[t1] > C[t2]
    def TermGtTerm(Term1 : (Int, Int), Term2 : (Int, Int), alloc : Int) : Int = {
      val (c1, t1) = Term1
      val (c2, t2) = Term2
      val iBit = T(c1, t1)
      val jBit = T(c2, t2)

      // e_bits[b]: bit (bits-b) of i and j are equal
      var e_bits = List() : List[Int]
      for (b <- 1 to BITS) yield {
        // iBit[bits - b] = jBit[bits - b]
        val eq = allocate(alloc)
        gt.iff(eq, new VecInt(List(iBit + BITS - b, jBit + BITS - b).toArray))

        if (b == 1) {
          e_bits = e_bits :+ eq
        } else {
          val e = allocate(alloc)
          gt.and(e, e_bits.last, eq)
          e_bits = e_bits :+ e
        }
      }

      var m_bits = List() : List[Int]

      // m_bits[b]: bits [bits..(bits-b)] of i are greater than j
      for (b <- 1 to BITS) {
        val bit_gt = allocate(alloc)
        gt.and(bit_gt, (iBit + BITS - b), -(jBit + BITS - b))

        if (b == 1) {
          m_bits = m_bits :+ bit_gt
        } else {
          val prev_eq = e_bits(b-2)
          val opt1 = allocate(alloc)
          gt.and(opt1, prev_eq, bit_gt)

          val opt2 = m_bits(b-2)

          val m = allocate(alloc)
          gt.or(m, new VecInt(List(opt1, opt2).toArray))
          m_bits = m_bits :+ m
        }
      }
      m_bits.last
    }


    def AddInitialColumn() = {
      slackvars = slackvars :+ 0

      for (t <- terms) {
        if ((domains.getOrElse(t, Set())).size == 0) {
          val identity = TermEqInt((0, t), t, 0)
          solver.addClause(new VecInt(List(identity).toArray))
        } else {
          val assBits = for (tt <- domains(t)) yield  {
            val tmpBit = TermEqInt((0, t), tt, 0)
            assignments((t, tt)) = tmpBit
            tmpBit
          }
          solver.addClause(new VecInt(assBits.toArray))
        }
      }
    }

    def AddDerivedColumn(Column : Int) = {
      slackvars = slackvars :+ 0
      val alloc = Column

      // For all pairs of functions with identical function symbols and different results,
      // form a three-tuple of (v_ij, (arg_i, s_i), (arg_j, s_j))
      val V = 
        for ((f_i, args_i, s_i) <- functions;
          (f_j, args_j, s_j) <- functions;
          if (f_i == f_j && s_i != s_j)) yield {
          var argBits = for (i <- 0 until args_i.length) yield TermEqTerm((Column-1, args_i(i)), (Column-1,args_j(i)), alloc)

          // argBit <=> C_p[args_i] = C_p[args_j]
          val argBit = allocate(alloc)
          gt.and(argBit, new VecInt(argBits.toArray))

          // gtBit <=> C_p[s_i] > C_p[s_j]
          val gtBit = TermGtTerm((Column-1, s_i), (Column-1, s_j), alloc)

          // vBit <=> args_i = args_j ^ s_i > s_j
          val vBit = allocate(Column)
          gt.and(vBit, argBit, gtBit)

          (vBit, (args_i, s_i), (args_j, s_j))
        }


      for (t <- terms) {
        // --- CASE1: Not a representing term ---

        for (tt <- terms; if t != tt) {
          val eqBit = TermEqInt((Column-1, t), tt, alloc)
          val asBit = TermEqTerm((Column, t), (Column, tt), alloc)

          // C_p[t] = tt ==> C_c[t] = C_c[tt]
          solver.addClause(new VecInt(List(-eqBit, asBit).toArray))
        }

        // --- CASE2: Representing term ---

        // is this term allowed to be identity

        val noVBits = 
          for ((vBit, (args_i, s_i), (args_j, s_j)) <- V) yield {

            // C_p[s_i] = t
            val eqBit = TermEqInt((Column-1, s_i), t, alloc)
            val ineqBit = allocate(Column)
            gt.not(ineqBit, eqBit)

            val noVBit = allocate(Column)

            // noVBit <=> !V ^ C_p[s_i] != t
            gt.or(noVBit, new VecInt(List(ineqBit, -vBit).toArray))
            noVBit
        }


        // vFalseBit <=> No V is true
        val vFalseBit = allocate(Column)
        gt.and(vFalseBit, new VecInt(noVBits.toArray))



        // C_c[t] = t
        val eqBit = TermEqInt((Column, t), t, alloc)

        val identityBit = allocate(Column)
        gt.and(identityBit, vFalseBit, eqBit)

        val funcBits = 
          for ((vBit, (args_i, s_i), (args_j, s_j)) <- V) yield {
            // C_p[s_i] = t
            val prevEqBit = TermEqInt((Column - 1, s_i), t, alloc)

            // C_c[t] = C_c[s_j]
            val curEqBit = TermEqTerm((Column, t), (Column, s_j), alloc)

            val fBit = allocate(Column)
            gt.and(fBit, new VecInt (List(vBit, prevEqBit, curEqBit).toArray))
            fBit
          }

        val functionalityBit = allocate(Column)
        if (funcBits.length == 0) {
          gt.gateFalse(functionalityBit)
        } else {
          gt.or(functionalityBit, new VecInt(funcBits.toArray))
        }

        // C_p[t] = t
        val isRepresentative = TermEqInt((Column-1, t), t, alloc)

        // C_p[t] = t ==> (C_c[t] = t v C_c[t] = s) for some functionality (t = s)
        // Either: not representative OR allowed identity OR derived functionality
        solver.addClause(new VecInt(List(-isRepresentative, identityBit, functionalityBit).toArray))
      }
    }

    // Make sure goal variables are removed at "POP"
    def AddGoalConstraint(Column : Int, goals : List[List[(Int, Int)]]) = {
      val goalBits =
        for (g <- goals) yield {
          val subGoals = for ((s, t) <- g)  yield TermEqTerm((Column, s), (Column, t), Column)
          val subGoal = allocate(Column)
          gt.and(subGoal, new VecInt(subGoals.toArray))
          subGoal
        }

      solver.addClause(new VecInt(goalBits.toArray))
    }

    def AddCompletionConstraint(Column : Int) = {
      val diff = for (t <- terms) yield (-TermEqTerm((Column-1, t), (Column, t), Column))
      solver.addClause(new VecInt(diff.toArray))
    }

    // MAIN SOLVE LOOP

    solver.reset()

    // prepare the solver to accept MAXVAR variables.MANDATORY
    solver.newVar (MAXVAR);

    var COLUMN = 1
    var cont = true

    var Model = None : Option[Array[Int]]
    AddInitialColumn()
    while (cont) {
      AddDerivedColumn(COLUMN)
      val goalConstraint = AddGoalConstraint(COLUMN, goals)

      if (solver.isSatisfiable()) {
        Model = Option(solver.model)
        cont = false
      } else {
        // More info?
        solver.removeConstr(goalConstraint)
        val completionConstraint = AddCompletionConstraint(COLUMN)
        if (solver.isSatisfiable()) {
          // Yes
          solver.removeConstr(completionConstraint)
          COLUMN += 1
        } else {
          // No
          Model = None
          cont = false
        }
      }
    }
    // println("Constraint count: " + solver.nConstraints())
    (Model, assignments)
  }

  def solve(Terms : List[TERM], Domains : Map[TERM, Set[TERM]], Goals : List[List[(TERM, TERM)]], Functions : List[(FUNC, List[TERM], TERM)]) : Option[Map[TERM, TERM]]= {
    var TermToInt = Map() : Map[TERM, Int] 
    var IntToTerm = Map() : Map[Int, TERM] 

    for (i <- 0 until Terms.length) {
      TermToInt(Terms(i)) = i
      IntToTerm(i) = Terms(i)
    }

    val terms = Terms.map(TermToInt)
    var domains = Map() : Map[Int, Set[Int]]
    for ((k, v) <- Domains) domains(TermToInt(k)) = v.map(TermToInt)
    val goals = Goals.map(g => g.map(x => { val (s,t) = x; (TermToInt(s), TermToInt(t)) }))
    val functions = Functions.map(x => { val(f, args, r) = x; (f, args.map(TermToInt), TermToInt(r)) })

    solveaux(terms, domains, goals, functions, true) match {
      case (Some(model), assignments) => {
        var assMap = Map() : Map[TERM, TERM]
        for (((variable, value), bit) <- assignments; 
          if model contains bit)
          assMap(IntToTerm(variable)) = IntToTerm(value)

        Some(assMap)
      }
      case (None, _) => {
        None
      }
    }
  }


  //
  //
  //  PARALLEL SOLVER
  //
  //

  // def parallel_solveaux(tables : Int, terms : List[Int], domains : Map[Int, Set[Int]], goals : List[List[List[(Int, Int)]]], functions : List[List[(FUNC, List[Int], Int)]], debug : Boolean) : (Option[Array[Int]], Map[(Int, Int), Int]) = {

  //   // We can put the slack after all the tables
  //   var slackvars = scala.collection.mutable.MutableList() : scala.collection.mutable.MutableList[Int]

  //   // Works as before
  //   var assignments = Map() : Map[(Int, Int), Int]

  //   // Same
  //   val BITS = binlog(terms.length)

  //   //
  //   // UTILITY FUNCTIONS
  //   //

  //   // Access Table[Column][Row]
  //   def T(Column : Int, Row : Int) : Int = 1 + Column*(terms.length)*BITS + slackvars.take(Column).sum + Row*BITS

  //   // allocate a new variable
  //   def allocate(Column : Int) : Int = {
  //     val newBit = T(Column + 1, 0)
  //     slackvars(Column) += 1
  //     newBit
  //   }


  //   //
  //   //  TERM EQUALITY FUNCTION
  //   // 

  //   // C[t] == i
  //   def TermEqInt(term : (Int, Int), i : Int, alloc : Int) : Int = {
  //     val (c, t) = term

  //     // TODO: Optimize
  //     var lits = List() : List[Int]
  //     var curBit = T(c, t)
  //     var curVal = i
  //     while (curVal > 0) {
  //       if (curVal % 2 == 1) {
  //         lits ::= curBit
  //         curVal -= 1
  //       } else {
  //         lits ::= -curBit
  //       }
  //       curBit += 1
  //       curVal /= 2
  //     }

  //     while (lits.length < BITS) {
  //       lits ::= -curBit
  //       curBit += 1
  //     }

  //     val prevBit = allocate(alloc)
  //     gt.and(prevBit, new VecInt(lits.toArray))
  //     prevBit
  //   }

  //   // C[t1] == C[t2]
  //   def TermEqTerm(Term1 : (Int, Int), Term2 : (Int, Int), alloc : Int) : Int = {
  //     val (c1, t1) = Term1
  //     val (c2, t2) = Term2
  //     val iBit = T(c1, t1)
  //     val jBit = T(c2, t2)

  //     val eqBits = 
  //       for (b  <- 0 until BITS) yield {
  //         val tmpBit = allocate(alloc)
  //         gt.iff(tmpBit, new VecInt(List(iBit + b, jBit + b).toArray))
  //         tmpBit
  //       }

  //     val eqBit = allocate(alloc)
  //     gt.and(eqBit, new VecInt(eqBits.toArray))
  //     eqBit
  //   }

  //   // C[t1] > C[t2]
  //   def TermGtTerm(Term1 : (Int, Int), Term2 : (Int, Int), alloc : Int) : Int = {
  //     val (c1, t1) = Term1
  //     val (c2, t2) = Term2
  //     val iBit = T(c1, t1)
  //     val jBit = T(c2, t2)

  //     // e_bits[b]: bit (bits-b) of i and j are equal
  //     var e_bits = List() : List[Int]
  //     for (b <- 1 to BITS) yield {
  //       // iBit[bits - b] = jBit[bits - b]
  //       val eq = allocate(alloc)
  //       gt.iff(eq, new VecInt(List(iBit + BITS - b, jBit + BITS - b).toArray))

  //       if (b == 1) {
  //         e_bits = e_bits :+ eq
  //       } else {
  //         val e = allocate(alloc)
  //         gt.and(e, e_bits.last, eq)
  //         e_bits = e_bits :+ e
  //       }
  //     }

  //     var m_bits = List() : List[Int]

  //     // m_bits[b]: bits [bits..(bits-b)] of i are greater than j
  //     for (b <- 1 to BITS) {
  //       val bit_gt = allocate(alloc)
  //       gt.and(bit_gt, (iBit + BITS - b), -(jBit + BITS - b))

  //       if (b == 1) {
  //         m_bits = m_bits :+ bit_gt
  //       } else {
  //         val prev_eq = e_bits(b-2)
  //         val opt1 = allocate(alloc)
  //         gt.and(opt1, prev_eq, bit_gt)

  //         val opt2 = m_bits(b-2)

  //         val m = allocate(alloc)
  //         gt.or(m, new VecInt(List(opt1, opt2).toArray))
  //         m_bits = m_bits :+ m
  //       }
  //     }
  //     m_bits.last
  //   }


  //   def AddInitialColumn() = {
  //     slackvars = slackvars :+ 0

  //     for (t <- terms) {
  //       if ((domains.getOrElse(t, Set())).size == 0) {
  //         val identity = TermEqInt((0, t), t, 0)
  //         solver.addClause(new VecInt(List(identity).toArray))
  //       } else {
  //         val assBits = for (tt <- domains(t)) yield  {
  //           val tmpBit = TermEqInt((0, t), tt, 0)
  //           assignments((t, tt)) = tmpBit
  //           tmpBit
  //         }
  //         solver.addClause(new VecInt(assBits.toArray))
  //       }
  //     }
  //   }

  //   def AddDerivedColumn(Column : Int) = {
  //     slackvars = slackvars :+ 0
  //     val alloc = Column

  //     // For all pairs of functions with identical function symbols and different results,
  //     // form a three-tuple of (v_ij, (arg_i, s_i), (arg_j, s_j))
  //     val V = 
  //       for ((f_i, args_i, s_i) <- functions;
  //         (f_j, args_j, s_j) <- functions;
  //         if (f_i == f_j && s_i != s_j)) yield {
  //         var argBits = for (i <- 0 until args_i.length) yield TermEqTerm((Column-1, args_i(i)), (Column-1,args_j(i)), alloc)

  //         // argBit <=> C_p[args_i] = C_p[args_j]
  //         val argBit = allocate(alloc)
  //         gt.and(argBit, new VecInt(argBits.toArray))

  //         // gtBit <=> C_p[s_i] > C_p[s_j]
  //         val gtBit = TermGtTerm((Column-1, s_i), (Column-1, s_j), alloc)

  //         // vBit <=> args_i = args_j ^ s_i > s_j
  //         val vBit = allocate(Column)
  //         gt.and(vBit, argBit, gtBit)

  //         (vBit, (args_i, s_i), (args_j, s_j))
  //       }


  //     for (t <- terms) {
  //       // --- CASE1: Not a representing term ---

  //       for (tt <- terms; if t != tt) {
  //         val eqBit = TermEqInt((Column-1, t), tt, alloc)
  //         val asBit = TermEqTerm((Column, t), (Column, tt), alloc)

  //         // C_p[t] = tt ==> C_c[t] = C_c[tt]
  //         solver.addClause(new VecInt(List(-eqBit, asBit).toArray))
  //       }

  //       // --- CASE2: Representing term ---

  //       // is this term allowed to be identity

  //       val noVBits = 
  //         for ((vBit, (args_i, s_i), (args_j, s_j)) <- V) yield {

  //           // C_p[s_i] = t
  //           val eqBit = TermEqInt((Column-1, s_i), t, alloc)
  //           val ineqBit = allocate(Column)
  //           gt.not(ineqBit, eqBit)

  //           val noVBit = allocate(Column)

  //           // noVBit <=> !V ^ C_p[s_i] != t
  //           gt.or(noVBit, new VecInt(List(ineqBit, -vBit).toArray))
  //           noVBit
  //       }


  //       // vFalseBit <=> No V is true
  //       val vFalseBit = allocate(Column)
  //       gt.and(vFalseBit, new VecInt(noVBits.toArray))



  //       // C_c[t] = t
  //       val eqBit = TermEqInt((Column, t), t, alloc)

  //       val identityBit = allocate(Column)
  //       gt.and(identityBit, vFalseBit, eqBit)

  //       val funcBits = 
  //         for ((vBit, (args_i, s_i), (args_j, s_j)) <- V) yield {
  //           // C_p[s_i] = t
  //           val prevEqBit = TermEqInt((Column - 1, s_i), t, alloc)

  //           // C_c[t] = C_c[s_j]
  //           val curEqBit = TermEqTerm((Column, t), (Column, s_j), alloc)

  //           val fBit = allocate(Column)
  //           gt.and(fBit, new VecInt (List(vBit, prevEqBit, curEqBit).toArray))
  //           fBit
  //         }

  //       val functionalityBit = allocate(Column)
  //       if (funcBits.length == 0) {
  //         gt.gateFalse(functionalityBit)
  //       } else {
  //         gt.or(functionalityBit, new VecInt(funcBits.toArray))
  //       }

  //       // C_p[t] = t
  //       val isRepresentative = TermEqInt((Column-1, t), t, alloc)

  //       // C_p[t] = t ==> (C_c[t] = t v C_c[t] = s) for some functionality (t = s)
  //       // Either: not representative OR allowed identity OR derived functionality
  //       solver.addClause(new VecInt(List(-isRepresentative, identityBit, functionalityBit).toArray))
  //     }
  //   }

  //   // Make sure goal variables are removed at "POP"
  //   def AddGoalConstraint(Column : Int, goals : List[List[(Int, Int)]]) = {
  //     val goalBits =
  //       for (g <- goals) yield {
  //         val subGoals = for ((s, t) <- g)  yield TermEqTerm((Column, s), (Column, t), Column)
  //         val subGoal = allocate(Column)
  //         gt.and(subGoal, new VecInt(subGoals.toArray))
  //         subGoal
  //       }

  //     solver.addClause(new VecInt(goalBits.toArray))
  //   }

  //   def AddCompletionConstraint(Column : Int) = {
  //     val diff = for (t <- terms) yield (-TermEqTerm((Column-1, t), (Column, t), Column))
  //     solver.addClause(new VecInt(diff.toArray))
  //   }

  //   // MAIN SOLVE LOOP

  //   solver.reset()

  //   // prepare the solver to accept MAXVAR variables.MANDATORY
  //   solver.newVar (MAXVAR);

  //   var COLUMN = 1
  //   var cont = true

  //   var Model = None : Option[Array[Int]]
  //   AddInitialColumn()
  //   while (cont) {
  //     AddDerivedColumn(COLUMN)
  //     val goalConstraint = AddGoalConstraint(COLUMN, goals)

  //     if (solver.isSatisfiable()) {
  //       Model = Option(solver.model)
  //       cont = false
  //     } else {
  //       // More info?
  //       solver.removeConstr(goalConstraint)
  //       val completionConstraint = AddCompletionConstraint(COLUMN)
  //       if (solver.isSatisfiable()) {
  //         // Yes
  //         solver.removeConstr(completionConstraint)
  //         COLUMN += 1
  //       } else {
  //         // No
  //         Model = None
  //         cont = false
  //       }
  //     }
  //   }
  //   // println("Constraint count: " + solver.nConstraints())
  //   (Model, assignments)
  // }

  // // Goals[i] should be solved by using Functions[i]
  // def parallel_solve(Terms : List[TERM], Domains : Map[TERM, Set[TERM]], Goals : List[List[List[(TERM, TERM)]]], Functions : List[List[(FUNC, List[TERM], TERM)]]) : Option[Map[TERM, TERM]]= {
  //   var TermToInt = Map() : Map[TERM, Int] 
  //   var IntToTerm = Map() : Map[Int, TERM] 

  //   for (i <- 0 until Terms.length) {
  //     TermToInt(Terms(i)) = i
  //     IntToTerm(i) = Terms(i)
  //   }

  //   val terms = Terms.map(TermToInt)
  //   var domains = Map() : Map[Int, Set[Int]]
  //   for ((k, v) <- Domains) domains(TermToInt(k)) = v.map(TermToInt)
  //   val goals = Goals.map(g => g.map(x => { val (s,t) = x; (TermToInt(s), TermToInt(t)) }))
  //   val functions = Functions.map(x => { val(f, args, r) = x; (f, args.map(TermToInt), TermToInt(r)) })

  //   solveaux(terms, domains, goals, functions, true) match {
  //     case (Some(model), assignments) => {
  //       var assMap = Map() : Map[TERM, TERM]
  //       for (((variable, value), bit) <- assignments; 
  //         if model contains bit)
  //         assMap(IntToTerm(variable)) = IntToTerm(value)

  //       Some(assMap)
  //     }
  //     case (None, _) => {
  //       None
  //     }
  //   }
  // }





}
