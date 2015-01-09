package ccu;

import org.sat4j.core._
import org.sat4j.specs._
import org.sat4j.minisat._
import org.sat4j.tools._

import ap.util.Timer

import scala.collection.mutable.{Map => MMap}

class Allocator(init : Int) {
  var next = init

  def alloc(count : Int) = {
    val ret = next
    next = next + count
    ret
  }
}

class Table[FUNC](bits : Int, ROWS : Int, alloc : Allocator, gt : GateTranslator, 
  solver : ISolver, terms : List[Int], domains : Map[Int, Set[Int]], 
  functions : List[(FUNC, List[Int], Int)] ) {

  var columnStartBit = List() : List[Int]
  var currentColumn = 0

  //
  // UTILITY FUNCTIONS
  //

  // Access Table[Column][Row]
  // TODO change to ()
  def apply(col : Int, row : Int) = columnStartBit(col) + row*bits

  //
  //  TERM EQUALITY FUNCTION
  //

  // C[t] == i
  def termEqInt(term : (Int, Int), i : Int) : Int = {
    ap.util.Timer.measure("termEqInt") {
    val (c, t) = term

    // TODO: Optimize
    var lits = List() : List[Int]
    var curBit = this(c, t)
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

    while (lits.length < bits) {
      lits ::= -curBit
      curBit += 1
    }

    val prevBit = alloc.alloc(1)
    gt.and(prevBit, new VecInt(lits.toArray))
    prevBit
  }
  }

  // C[t1] == C[t2]
  def termEqTerm(term1 : (Int, Int), term2 : (Int, Int)) : Int = {
    ap.util.Timer.measure("termEqTerm") {
    val allocNext = alloc.next
    var used = 0

    val (c1, t1) = term1
    val (c2, t2) = term2
    val iBit = this(c1, t1)
    val jBit = this(c2, t2)

    val eqBits =
      for (b  <- 0 until bits) yield {
        val tmpBit = allocNext + used
        used += 1
        gt.iff(tmpBit, new VecInt(List(iBit + b, jBit + b).toArray))
        tmpBit
      }

    val eqBit = allocNext + used
    used += 1
    gt.and(eqBit, new VecInt(eqBits.toArray))
    alloc.alloc(used)
    eqBit
  }
  }

  // C[t1] > C[t2]
  def termGtTerm(term1 : (Int, Int), term2 : (Int, Int)) : Int = {
    ap.util.Timer.measure("termGtTerm") {
    val allocNext = alloc.next
    var used = 0

    val (c1, t1) = term1
    val (c2, t2) = term2
    val iBit = this(c1, t1)
    val jBit = this(c2, t2)

    // e_bits[b]: bit (bits-b) of i and j are equal
    var e_bits = List() : List[Int]
    for (b <- 1 to bits) yield {
      // iBit[bits - b] = jBit[bits - b]
      val eq = allocNext + used
      used += 1
      gt.iff(eq, new VecInt(List(iBit + bits - b, jBit + bits - b).toArray))

      if (b == 1) {
        e_bits = e_bits :+ eq
      } else {
        val e = allocNext + used
        used += 1 
        gt.and(e, e_bits.last, eq)
        e_bits = e_bits :+ e
      }
    }

    var m_bits = List() : List[Int]

    // m_bits[b]: bits [bits..(bits-b)] of i are greater than j
    for (b <- 1 to bits) {
      val bit_gt = allocNext + used
      used += 1
      gt.and(bit_gt, (iBit + bits - b), -(jBit + bits - b))

      if (b == 1) {
        m_bits = m_bits :+ bit_gt
      } else {
        val prev_eq = e_bits(b-2)
        val opt1 = allocNext + used
        used += 1
        gt.and(opt1, prev_eq, bit_gt)

        val opt2 = m_bits(b-2)

        val m = allocNext + used
        used += 1
        gt.or(m, new VecInt(List(opt1, opt2).toArray))
        m_bits = m_bits :+ m
      }
    }
    alloc.alloc(used)
    m_bits.last
  }
  }


  def addInitialColumn() = {
    ap.util.Timer.measure("addInitialColumn") {
    columnStartBit = columnStartBit :+ alloc.alloc(ROWS*bits)

    val assignments = MMap() : MMap[(Int, Int), Int]

    for (t <- terms) {
      if ((domains.getOrElse(t, Set())).size == 0) {
        val identity = termEqInt((0, t), t)
        val asd = new VecInt(List(identity).toArray)
        solver.addClause(asd)
      } else {
        val assBits = for (tt <- domains(t)) yield  {
          val tmpBit = termEqInt((0, t), tt)
          assignments((t, tt)) = tmpBit
          tmpBit
        }
        val asd = new VecInt(assBits.toArray)
        solver.addClause(asd)
      }
    }

    assignments
  }
  }

  def addDerivedColumn() = {
    ap.util.Timer.measure("addDerivedColumn") {
      // For all pairs of functions with identical function symbols and different results,
      // form a three-tuple of (v_ij, (arg_i, s_i), (arg_j, s_j))
      currentColumn += 1
      columnStartBit = columnStartBit :+ alloc.alloc(ROWS*bits)

      val eqBits = Array.tabulate(terms.length, terms.length)( (x, y) => -1)


      val V =
        for ((f_i, args_i, s_i) <- functions;
          (f_j, args_j, s_j) <- functions;
          if (f_i == f_j && s_i != s_j)) yield {
          var argBits = for (i <- 0 until args_i.length) yield {
            val t1 = args_i(i) min args_j(i)
            val t2 = args_i(i) max args_j(i)
            if (eqBits(t1)(t2) == -1)
              eqBits(t1)(t2) = termEqTerm((currentColumn-1, args_i(i)), (currentColumn-1,args_j(i)))
            eqBits(t1)(t2)
          }
          // argBit <=> C_p[args_i] = C_p[args_j]
          val argBit = alloc.alloc(1)
          gt.and(argBit, new VecInt(argBits.toArray))

          // gtBit <=> C_p[s_i] > C_p[s_j]
          val gtBit = termGtTerm((currentColumn-1, s_i), (currentColumn-1, s_j))

          // vBit <=> args_i = args_j ^ s_i > s_j
          val vBit = alloc.alloc(1)
          gt.and(vBit, argBit, gtBit)

          (vBit, (args_i, s_i), (args_j, s_j))
        }


      for (t <- terms) {
        // --- CASE1: Not a representing term ---

        for (tt <- terms; if t != tt) {
          val eqBit = termEqInt((currentColumn-1, t), tt)
          val asBit = termEqTerm((currentColumn, t), (currentColumn, tt))

          // C_p[t] = tt ==> C_c[t] = C_c[tt]
          val asd = new VecInt(List(-eqBit, asBit).toArray)
          solver.addClause(asd)
        }

        // --- CASE2: Representing term ---

        // is this term allowed to be identity

        val noVBits =
          for ((vBit, (args_i, s_i), (args_j, s_j)) <- V) yield {

            // C_p[s_i] = t
            val eqBit = termEqInt((currentColumn-1, s_i), t)
            val ineqBit = alloc.alloc(1)
            gt.not(ineqBit, eqBit)

            val noVBit = alloc.alloc(1)

            // noVBit <=> !V ^ C_p[s_i] != t
            gt.or(noVBit, new VecInt(List(ineqBit, -vBit).toArray))
            noVBit
          }


        // vFalseBit <=> No V is true
        val vFalseBit = alloc.alloc(1)
        gt.and(vFalseBit, new VecInt(noVBits.toArray))



        // C_c[t] = t
        val eqBit = termEqInt((currentColumn, t), t)

        val identityBit = alloc.alloc(1)
        gt.and(identityBit, vFalseBit, eqBit)

        val funcBits =
          for ((vBit, (args_i, s_i), (args_j, s_j)) <- V) yield {
            // C_p[s_i] = t
            val prevEqBit = termEqInt((currentColumn - 1, s_i), t)

            // C_c[t] = C_c[s_j]
            val curEqBit = termEqTerm((currentColumn, t), (currentColumn, s_j))

            val fBit = alloc.alloc(1)
            gt.and(fBit, new VecInt (List(vBit, prevEqBit, curEqBit).toArray))
            fBit
          }

        val functionalityBit = alloc.alloc(1)
        if (funcBits.length == 0) {
          gt.gateFalse(functionalityBit)
        } else {
          gt.or(functionalityBit, new VecInt(funcBits.toArray))
        }

        // C_p[t] = t
        val isRepresentative = termEqInt((currentColumn-1, t), t)

        // C_p[t] = t ==> (C_c[t] = t v C_c[t] = s) for some functionality (t = s)
        // Either: not representative OR allowed identity OR derived functionality
        val asd = new VecInt(List(-isRepresentative, identityBit, functionalityBit).toArray)
        solver.addClause(asd)
      }
    }
  }

  // Make sure goal variables are removed at "POP"
  def addGoalConstraint(goals : List[List[(Int, Int)]]) = {
    ap.util.Timer.measure("addGoalConstraint") {
    val goalBits =
      for (g <- goals) yield {
        val subGoals = for ((s, t) <- g)  yield termEqTerm((currentColumn, s), (currentColumn, t))
        val subGoal = alloc.alloc(1)
        gt.and(subGoal, new VecInt(subGoals.toArray))
        subGoal
      }

    val asd = new VecInt(goalBits.toArray)
    solver.addClause(asd)
  }
  }

  def addCompletionConstraint() = {
    ap.util.Timer.measure("addCompletionConstraint") {
    val diff = for (t <- terms) yield (-termEqTerm((currentColumn-1, t), (currentColumn, t)))
    val asd = new VecInt(diff.toArray)
    solver.addClause(asd)
  }
  }
}

class CCUSolver[TERM, FUNC] {

  // SAT4J stuff
  val asd = (ap.util.Timer.measure("SAT4Jinit") {
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
  def disequalityCheck(eq : Array[Array[Int]], functions : List[(FUNC, List[Int], Int)]) = {
    var changed = true
    while (changed) {
      changed = false

      // Functionality
      for ((f_i, args_i, s_i) <- functions;
        (f_j, args_j, s_j) <- functions;
        if (f_i == f_j && s_i != s_j && eq(s_i min s_j)(s_i max s_j) == 0)) 
      {
        var equal = true
        for (i <- 0 until args_i.length) {
          if (eq(args_i(i) min args_j(i))(args_i(i) max args_j(i)) == 0) {
            equal = false
          }
        }
        if (equal) {
          eq(s_i)(s_j) = 1
          eq(s_j)(s_i) = 1
          changed = true
        }
      }

      // Transitivity
      for (i <- 0 until eq.length) {
        for (j <- 0 until eq.length) {
          for (k <- 0 until eq.length) {
            if (eq(i)(k) == 0 && eq(i)(j) == 1 && eq(j)(k) == 1) {
              eq(i)(k) = 1
              changed = true
            }
          }
        }
      }
    }
    eq
  }


  // 
  // MATH HELPER FUNCTIONS
  //
  
  // Calculating log_2 (b)
  // Used for cacluating number of bits needed
  def binlog(b : Int) : Int = {
    ap.util.Timer.measure("binlog") {
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
  // SOLVER FUNCTIONS
  //
  def solveaux(
    terms : List[Int],
    domains : Map[Int, Set[Int]], 
    goals : List[List[(Int, Int)]], 
    functions : List[(FUNC, List[Int], Int)], 
    debug : Boolean) : (Option[Array[Int]], Map[(Int, Int), Int]) = {
    ap.util.Timer.measure("solveaux") {
    val rows = terms.length
    val bits = binlog(rows)
    val alloc = new Allocator(1)
    val table = new Table[FUNC](bits, rows, alloc, gt, solver, terms, domains, functions)
    solver.reset()

    // MAIN SOLVE LOOP
    var cont = true
    var model = None : Option[Array[Int]]
    var assignments = table.addInitialColumn()
    while (cont) {
      table.addDerivedColumn()
      val goalConstraint = table.addGoalConstraint(goals)

      ap.util.Timer.measure("solveaux_isSat") {
      if (solver.isSatisfiable()) {
        model = Option(solver.model)
        cont = false
      } else {
        // More info?
        ap.util.Timer.measure("solveaux_completionConstraint") {
          solver.removeConstr(goalConstraint)
          val completionConstraint = table.addCompletionConstraint()
          if (solver.isSatisfiable()) {
            // Yes
            solver.removeConstr(completionConstraint)
          } else {
            // No
            model = None
            cont = false
          }
        }
      }
      }
    }

    (model, assignments.toMap)
  }
  }

  def solve(
    terms : List[TERM],
    domains : Map[TERM, Set[TERM]],
    goals : List[List[(TERM, TERM)]], 
    functions : List[(FUNC, List[TERM], TERM)]) : Option[Map[TERM, TERM]] = {
    ap.util.Timer.measure("solve") {
    if (terms.isEmpty || goals.isEmpty) 
      return None
    for (g <- goals)
      if (g.isEmpty)
        return None

    // println("CCUSolver.solve()")
    // println("\tterms:" + terms)
    // println("\tdomains:" + domains)
    // println("\tgoals:" + goals)
    // println("\tfunctions:" + functions)

    // Convert to Int representation
    val termToInt = MMap() : MMap[TERM, Int] 
    val intToTerm = MMap() : MMap[Int, TERM] 

    for (i <- 0 until terms.length) {
      termToInt(terms(i)) = i
      intToTerm(i) = terms(i)
    }

    val newTerms = terms.map(termToInt)
    val newDomains = MMap() : MMap[Int, Set[Int]]
    for ((k, v) <- domains) newDomains(termToInt(k)) = v.map(termToInt)
    val newGoals = goals.map(g => g.map(x => { val (s,t) = x; (termToInt(s), termToInt(t)) }))
    val newFunctions = 
      functions.map(x => { val(f, args, r) = x; (f, args.map(termToInt), termToInt(r)) })

    // Solve and return UNSAT or SAT + model
    solveaux(newTerms, newDomains.toMap, newGoals, newFunctions, true) match {
      case (Some(model), assignments) => {
        val assMap = MMap() : MMap[TERM, TERM]
        for (((variable, value), bit) <- assignments; 
          if model contains bit)
          assMap(intToTerm(variable)) = intToTerm(value)

        Some(assMap.toMap)
      }
      case (None, _) =>  None
    }
  }
  }

  //
  //
  //  PARALLEL SOLVER
  //
  //

  def parallelSolveaux(
    terms : List[Int],
    domains : Map[Int, Set[Int]],
    goals : List[List[List[(Int, Int)]]], 
    functions : List[List[(FUNC, List[Int], Int)]], 
    debug : Boolean) : (Option[Array[Int]], Map[(Int, Int), Int]) = {
    ap.util.Timer.measure("parallelSolveaux") {
    // TODO: optimize such that each table has its own rows
    val rows = terms.length
    // TODO: optimize such that each table has its own bits
    val bits = binlog(rows)
    // Alloc must be shared between tables
    val alloc = new Allocator(1)

    // HACK?
    val problemCount = goals.length

    val tables = 
      for (p <- 0 until problemCount) yield
        new Table[FUNC](bits, rows, alloc, gt, solver, terms, domains, functions(p))
    solver.reset()

    // MAIN SOLVE LOOP
    var cont = true
    var model = None : Option[Array[Int]]

    // TODO: change if tables has different rows
    val assignments = for (p <- 0 until problemCount) yield tables(p).addInitialColumn()

    // Since all table have same domain, they should have same assginments
    if (problemCount > 1) {
      for (((variable, value), bit) <- assignments(0)) {
        val tmpBit = alloc.alloc(1)
        val lits = for (ass <- assignments) yield ass((variable, value))
        gt.iff(tmpBit, new VecInt(lits.toArray))
        solver.addClause(new VecInt(List(tmpBit).toArray))
      }
    }


    while (cont) {
      for (p <- 0 until problemCount)
        tables(p).addDerivedColumn()

      val goalConstraints =
        for (p <- 0 until problemCount) yield
          tables(p).addGoalConstraint(goals(p))

      ap.util.Timer.measure("parallelSolve_isSat") {
      if (solver.isSatisfiable()) {
        model = Option(solver.model)
        cont = false
      } else {
        ap.util.Timer.measure("parallelSolve_completionConstraint") {
        // More info?
        for (gc <- goalConstraints)
          solver.removeConstr(gc)

        // TODO: Make disjunction
        val completionConstraints = 
        for (p <- 0 until problemCount) yield
          tables(p).addCompletionConstraint()

        if (solver.isSatisfiable()) {
          // Yes
          for (cc <- completionConstraints)
            solver.removeConstr(cc)
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
    (model, assignments(0).toMap)
  }
  }

  // Given a list of domains, goals, functions, see if there is a solution to
  // the simultaneous problem. 

  def parallelSolve(
    terms : List[TERM],
    domains : Map[TERM, Set[TERM]],
    goals : List[List[List[(TERM, TERM)]]], 
    functions : List[List[(FUNC, List[TERM], TERM)]]) = {
    ap.util.Timer.measure("parallelSolve") {   
    // TODO: Build up terms automatically

    // HACK?
    val problemCount = goals.length

    // Convert to Int representation
    var termToInt = Map() : Map[TERM, Int] 
    var intToTerm = Map() : Map[Int, TERM] 

    for (i <- 0 until terms.length) {
      termToInt += (terms(i) -> i)
      intToTerm += (i -> terms(i))
    }

    val newTerms = terms.map(termToInt)

    var newDomains = Map() : Map[Int, Set[Int]]
    for ((k, v) <- domains)
      newDomains += (termToInt(k) -> v.map(termToInt))

    val newGoals =
      for (g <- goals)
      yield (for (eqs <- g)
             yield for ((s, t) <- eqs) yield (termToInt(s), termToInt(t)))

    val newFunctions =
      for (funs <- functions)
      yield (for ((f, args, r) <- funs)
             yield (f, args.map(termToInt), termToInt(r)))

    // Solve and return UNSAT or SAT + model
    parallelSolveaux(newTerms, newDomains.toMap, newGoals, newFunctions, true) match {
      case (Some(model), assignments) => {
        var assMap = Map() : Map[TERM, TERM]
        for (((variable, value), bit) <- assignments; 
          if model contains bit)
          assMap += (intToTerm(variable) -> intToTerm(value))

        Some(assMap)
      }
      case (None, _) =>  None
    }
  }
  }

}
