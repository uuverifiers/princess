// 	convALL0 != DUMMY_TERM_0^every_one_but(convALL1, DUMMY_TERM_0)) v !hates(convALL1, convALL0))
// Maybe use triple-disjunction instead?

/**
 * This file is part of ePrincess, a theorem prover based on 
 * Bounded Rigid E-Unification (http://user.it.uu.se/~petba168/breu/) 
 * incoporated into the Princess theorem prover
 * <http://www.philipp.ruemmer.org/princess.shtml>
 * 
 * Copyright (C) 2009-2016 Peter Backeman <peter@backeman.se>
 * Copyright (C) 2009-2016 Philipp Ruemmer <ph_r@gmx.net>
 *
 * ePrincess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * ePrincess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with ePrincess.  If not, see <http://www.gnu.org/licenses/>.
 */


// TODO RIGHT NOW:
//
// Line 705 fix on geo118+1.p
// TODO: Fix terms vs order (BREUterms?)

package ap.connection;

import ap.terfor.{TermOrder, ConstantTerm}
import ap.terfor.conjunctions.{Conjunction, Quantifier}
import ap.terfor.preds.{Atom, PredConj, Predicate}
import ap.terfor.arithconj.ArithConj
import ap.terfor.linearcombination.LinearCombination
import ap.proof.goal.Goal
import ap.util.{Debug, Timer, Combinatorics, Seqs}
import ap.parameters.{GoalSettings, Param}
import ap.proof.Vocabulary
import ap.connection.connection.BREUOrder
import scala.collection.mutable.{ListBuffer}

object ConnectionProver {
  val AC = Debug.AC_CONNECTION_PROVER
}


class ConnectionProver(depthFirst : Boolean, preSettings : GoalSettings, strong : Boolean, DEBUGPrint : Boolean = false) {
  // How many of our closing-attempts could easily be ignored
  var safeSKIP = 0

  val DEBUG = true

  def dprintln(str : String) = if (DEBUGPrint) println(str)

  // TODO: How to make this nicer?
  var nextPredicate = 0
  var nextTerm = 0


  /**
    * Instantiate top-level of conjuction, returning instantiated conj, updated BREUorder and TermOrder 
    */
  def inst(conj : Conjunction, prefix : String, order : TermOrder) : (Conjunction, BREUOrder, TermOrder) = {
    var allCount = -1
    var exCount = -1

    val quants =
      for (q <- conj.quans) yield {
        q match { 
          case Quantifier.ALL => {
            allCount += 1
            (new ConstantTerm(prefix + "ALL" + allCount), true)
          }
          case Quantifier.EX => {
            exCount += 1
            (new ConstantTerm(prefix + "EX" + exCount), false)
          }
        }
      }

    val newOrder = order.extend(quants.map(_._1))
    val res = conj.instantiate(quants.map(_._1))(newOrder)
    (res, quants.toList, newOrder)
  }

  var depth = 0
  def i() = depth += 1
  def d() = depth -= 1
  def p(str : String) = println("\t"*depth + str)

  /**
    * Instantiates conj, where new terms are named using prefix. 
    * 
    *  Returns: 
    *    -Instantiated Conjunction,
    *    -New constant terms (and a Boolean indicating if they are Universally Quantified)
    *    -Updated TermOrder (which might be thrown away...)
    */
  def instantiateAux(conj : Conjunction, prefix : String, to : TermOrder) :
      (Conjunction, List[(ConstantTerm, Boolean)], TermOrder) = {
    
    // Instantiate top-level
    val allTerms : ListBuffer[(ConstantTerm, Boolean)] = ListBuffer()

    val (newConj, nt, norder) = inst(conj, prefix, to)
    allTerms ++= nt

    var disjCount = 0    
    var termOrder = norder

    val updatedNegatedConjs =
      for (disjunction <- newConj.negatedConjs) yield {
        val (negConj, nt, no) = instantiateAux(disjunction, prefix + "_disj" + disjCount, termOrder)
        disjCount += 1
        termOrder = no
        allTerms ++= nt
        negConj
      }

    val finalConj = 
      if (!updatedNegatedConjs.isEmpty) {
        val negConj = newConj.negatedConjs.update(updatedNegatedConjs, termOrder)
        newConj.updateNegatedConjs(negConj)(termOrder)
      } else {
        newConj
      }


    (finalConj, allTerms.toList.reverse, termOrder)
  }

  /**
    * 
    * Instantiate a formula
    * 
    * s.t. all quantifiers are instantiated with dummy variables
    * using prefix. 
    */
  def fullInst(conj : Conjunction, prefix : String) = {
    val (instConjunction, newTerms, _) = instantiateAux(conj, prefix, conj.order)
    (instConjunction, newTerms)
  }


  /**
    * Returns a clause with the selected literal in front:
    * 
    * We enumerate the literals in the clauses as:
    * cls = (0 v 1 v 2) ^ (3 v 4) ^ (5 v 6 v 7 v 8)
    * 
    * I.e.
    *  findLiteral(cls, 6) = (6 v 5 v 7 v 8)
    */
  def findLiteral(inputClauses : List[Conjunction], step : Int) : (Conjunction, Int) = {
    if (step >= clauseWidth(inputClauses.head)) {
      findLiteral(inputClauses.tail, step - clauseWidth(inputClauses.head))
    } else {
      (inputClauses.head, step)
    }
  }



  // STEP 0: Try closing as-is
  // STEP 1+: Where (x, y) is input clause x with literal y:
  //          try (0,0), (0,1), ... (1,0) ...

  /**
    * Try closing 
    */
  def tryStep(table : ConnectionTable, step : Int, branchIdx : Int, inputClauses : List[Conjunction],
    iteration : Int, disequalities : Seq[(ConstantTerm, ConstantTerm)]) : Option[ConnectionTable] = {
    dprintln("Trying step " + step)
    val closedTable =
      if (step == 0) {
        Some(table.close(branchIdx, strong))
      } else ap.util.Timer.measure("Extending Table") {
        val (clause, idx) = findLiteral(inputClauses, step - 1)
        val (instClause, newBREUOrder) = fullInst(clause, "branch_" + iteration)
        val (pseudoClause, tmpBREUOrder) = conjToClause(instClause)

        // TODO: tmpBREUOrder should only be existentials...
        val extendedTable = table.extendBranch(branchIdx, pseudoClause, idx, newBREUOrder ++ tmpBREUOrder)
        extendedTable.closeSafe(branchIdx, strong)
      }

    if (closedTable.isEmpty) {
      dprintln("SAFESKIP")
      safeSKIP += 1
      None
    } else ap.util.Timer.measure("Checking closable") {
      if (closedTable.get.closable(disequalities)) {
        closedTable
      } else {
        None
      }
    }
  }


  /*
   * SOLVE TABLE
   */
  def solveTable(
    table : ConnectionTable,
    inputClauses : List[Conjunction],
    maxIteration : Int,
    iteration : Int,
    disequalities : Seq[(ConstantTerm, ConstantTerm)]) :
      (Option[ConnectionTable], Boolean) = ap.util.Timer.measure("solveTable") {

    if (table.openBranches == 0) {
      // No open branches - we are done
      dprintln("All branches closed!")
      (Some(table), false)
    } else if (table.openBranches > maxIteration - iteration) {
      // We can't close n branches with <n iterations
      dprintln("Open Branches > Remaining Iterations")
      (None, true)
    } else {
      // Let's try one more step...

      // val branchIdx = table.firstOpen
      val branchIdx = table.shortestOpen

      // TODO: Any way of making branch a val and branchStep a var?
      println("\n//--------- " + iteration + " -------------")
      println("|| extending (" + branchIdx + ")")
      // println((for (l <- table.toString.split("\n").toList) yield ("|| " + l)).mkString("\n"))
      for (i <- table.branches.indices) {
        if (i == branchIdx)
          dprintln("|| --> " + table.branches(i))
        else
          dprintln("|| " + table.branches(i))
      }

      dprintln("||==============================")
      println(table)
      if (!disequalities.isEmpty)
        println("|| Disequalities: " + disequalities.mkString(", "))
      println("\\\\--------- " + iteration + " -------------\n")

      // We use the branchStep to decide where to search for the new candidate
      var maxReached = false
      // If this is the last iteration, only relevant action to close table right away
      val maxStep =
        if (iteration == maxIteration) {
          maxReached = true
          0
        } else {
          inputClauses.map(clauseWidth(_)).sum
        }

      var step = 0
      while (step <= maxStep) {
        val res = tryStep(table, step, branchIdx, inputClauses, iteration, disequalities)
        if (res.isDefined) {
          dprintln("\nStep (" + step + ") works!")
          val (t, mr) = solveTable(res.get, inputClauses, maxIteration, iteration + 1, res.get.diseqPairs.toList ++ disequalities)
          if (!t.isEmpty)
            return (t, mr)
          maxReached |= mr
        }
        step += 1
      }

      dprintln("BACKTRACK")
      (None, maxReached)
    }
  }



  //
  //
  //
  // CONVERSION TO CNF ...
  //
  //
  //
  //


  /**
    *  AND THIS IS UNDER DOUBLE NEGATION?

    * Here conj is pseudo-literal. 
    * This means it is an actual conjunction...
    * 
    * Here we sometimes get a negated conjunction. I do not know why...
    */
  def conjToPseudoLiteral(conj : Conjunction) : (List[FunEquation], Node) = {
    dprintln("conjToPseudo(" + conj + ")")
    val funPreds = Param.FUNCTIONAL_PREDICATES(preSettings)    
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, conj.arithConj.positiveEqs.size == 0)
    Debug.assertInt(ConnectionProver.AC, conj.arithConj.negativeEqs.size <= 1)
    Debug.assertInt(ConnectionProver.AC, conj.negatedConjs.size == 0)    
    //-END-ASSERTION-//////////////////////////////////////////////////////////

    val funEqs =
      (for (p <- conj.predConj.positiveLits.iterator; if p.predicates subsetOf funPreds) yield FunEquation(p)).toList

    val negFunEqs =
      (for (p <- conj.predConj.negativeLits.iterator; if p.predicates subsetOf funPreds) yield FunEquation(p)).toList


    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, negFunEqs.length == 0)
    //-END-ASSERTION-//////////////////////////////////////////////////////////    

    // Two cases, either we have a negative equation or a ordinary literal
    if (conj.arithConj.negativeEqs.size == 1) {
      dprintln("ArithEqs")
      val eq = conj.arithConj.negativeEqs(0)
      dprintln("\t" + eq)
      val (c, d, newOrder) = eqTerms(eq, conj.order)
      dprintln("\tc" + c)
      dprintln("\td" + d)
      // Should we update the order?
      val tempPred = new Predicate("tempPred_" + nextPredicate, 1)
      nextPredicate += 1
      val a1: Atom = Atom(tempPred, List(LinearCombination(c, newOrder)), newOrder)
      dprintln("\ta1: " + a1)
      val a2: Atom = Atom(tempPred, List(LinearCombination(d, newOrder)), newOrder)
      dprintln("\ta2: " + a2)            
      val ret = (List(FunEquation(a1), FunEquation(a2)), NegEquation(c, d))
      dprintln("\tret: " + ret)
      ret
    } else {
      // There should only be one non-equational literal
      val posPredLits =
        (for (p <- conj.predConj.positiveLits.iterator; if !(p.predicates subsetOf funPreds)) yield PositiveLiteral(p)).toList

      val negPredLits =
        (for (p <- conj.predConj.negativeLits.iterator; if !(p.predicates subsetOf funPreds)) yield NegativeLiteral(p)).toList

      dprintln("posPredLits: "+ posPredLits.mkString(","))
      dprintln("negPreDLtis: "+ negPredLits.mkString(","))
      //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
      Debug.assertInt(ConnectionProver.AC, posPredLits.length + negPredLits.length == 1)
      //-END-ASSERTION-//////////////////////////////////////////////////////////

      val lit = (posPredLits ++ negPredLits).toList.head
      (funEqs.toList, lit)
    }
  }

  private def toConstant(lc : LinearCombination, order : TermOrder) : (ConstantTerm, TermOrder) = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ConnectionProver.AC,
      (lc.isConstant &&
        (lc.constant.isZero || lc.constant.isOne)) ||
        (lc.size == 1 &&
          lc.leadingCoeff.isOne &&
          lc.leadingTerm.isInstanceOf[ConstantTerm]))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    if (lc.isConstant) {
      val c = new ConstantTerm ("int_" + lc.constant)
      (c, order.extend(c))
    } else {
      (lc.leadingTerm.asInstanceOf[ConstantTerm], order)
    }
  }

  private def eqTerms(lc : LinearCombination, order : TermOrder) :  (ConstantTerm, ConstantTerm, TermOrder) = {
    lc.size match {
      case 1 => {
        val (c1, order1) = toConstant(lc, order)
        val (c2, order2) = toConstant(LinearCombination.ZERO, order1)
        (c1, c2, order2)
      }
      case 2 if (lc.constants.size == 1 && lc.leadingCoeff.isOne) =>
        val (c2, newOrder) = toConstant(LinearCombination(-lc.constant), order)
        (lc.leadingTerm.asInstanceOf[ConstantTerm], c2, newOrder)
      case 2 => {
        //-BEGIN-ASSERTION-////////////////////////////////////////////
        Debug.assertInt(ConnectionProver.AC,
          lc.size == 2 &&
            lc.getCoeff(0).isOne && lc.getCoeff(1).isMinusOne &&
            lc.getTerm(0).isInstanceOf[ConstantTerm] &&
            lc.getTerm(1).isInstanceOf[ConstantTerm])
        //-END-ASSERTION-//////////////////////////////////////////////
        
        (lc.getTerm(0).asInstanceOf[ConstantTerm], lc.getTerm(1).asInstanceOf[ConstantTerm], order)
      }
    }
  }

  /**
    *  THIS FUNCTION IS UNDER ONE NEGATION?
    * 
    * Here conj is a disjunction
    * Each literal in predConj.positiveLits/negativeLits is a literal
    * each conjunction in negatedConjs is a pseudo-lietral
    * 
    *  So it seems we should be able to put positive fun equations to other branches? (If we change quantifiers)
    */
  def disjunctionToClause(conj : Conjunction) : (PseudoClause, BREUOrder) = {
    dprintln("disjToClause(" + conj + ")")
    val funPreds = Param.FUNCTIONAL_PREDICATES(preSettings)
    var newBREUOrder = List() : BREUOrder
    var newOrder = conj.order
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, conj.arithConj.positiveEqs.size == 0)
    //-END-ASSERTION-//////////////////////////////////////////////////////////

    // val funEqs = 
    //   (for (p <- conj.predConj.positiveLits.iterator; if p.predicates subsetOf funPreds) yield FunEquation(p)).toList

    dprintln("ArithEqs")
    val arithEqs =
      (for (eq <- conj.arithConj.negativeEqs) yield {
        dprintln("" + eq)
        val (c, d, tmpOrder) = eqTerms(eq, newOrder)
        newOrder = tmpOrder
        dprintln("\tc" + c)
        dprintln("\td" + d)
        // Should we update the order?
        val tempPred = new Predicate("tempPred", 0)
        val a1: Atom = Atom(tempPred, List(LinearCombination(c, newOrder)), newOrder)
        val a2: Atom = Atom(tempPred, List(LinearCombination(d, newOrder)), newOrder)        
        List(FunEquation(a1), FunEquation(a2))
      }).flatten
    dprintln("\t..." + arithEqs.mkString(","))

    val negFunEqs = 
      (for (p <- conj.predConj.negativeLits.iterator; if p.predicates subsetOf funPreds) yield {
        val (feq, neq, tmpBREUOrder) = convertNegFunEq(p)
        newBREUOrder ++= tmpBREUOrder
        new PseudoLiteral(List(feq), neq)
      }).toList

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, negFunEqs.length == 0)
    //-END-ASSERTION-//////////////////////////////////////////////////////////


    // One of these should be negated...    
    val posPredLits =
      (for (p <- conj.predConj.positiveLits.iterator; if !(p.predicates subsetOf funPreds)) yield new PseudoLiteral(List(), NegativeLiteral(p))).toList

    val negPredLits =
      (for (p <- conj.predConj.negativeLits.iterator; if !(p.predicates subsetOf funPreds)) yield new PseudoLiteral(List(), PositiveLiteral(p))).toList


    // dprintln("posPreDLits: " + posPredLits)
    // dprintln("negPredLits: " + negPredLits)

    val pseudoLiterals =
      for (n <- conj.negatedConjs) yield {
        val (feq, lit) = conjToPseudoLiteral(n)
        new PseudoLiteral(feq, lit)
      }

    val funLiterals =
      for (p <- conj.predConj.positiveLits.iterator; if p.predicates subsetOf funPreds) yield {
        val (feq, neq, tmpBREUOrder) = convertNegFunEq(p)
        newBREUOrder ++= tmpBREUOrder        
        new PseudoLiteral(List(feq), neq)
      }

    (new PseudoClause((negFunEqs ++ funLiterals ++ posPredLits ++ negPredLits ++ pseudoLiterals).toList), newBREUOrder)
  }

  // Converting one conjunction to a pseudoclause (which consists of consists pseudoliterals).
  // Three are two cases.
  // (A) It is a single positive or negative literal (this corresponds to a unit-clause)
  // (B) Negated conjs is larger than 0, and we have a disjunction (and then the predconj should be empty)
  def conjToClause(conj : Conjunction) : (PseudoClause, BREUOrder) = {
    // dprintln("conjToClause(" + conj + ")")
    val predConj = conj.predConj
    val funPreds = Param.FUNCTIONAL_PREDICATES(preSettings)        

    var breuOrder = List() : BREUOrder
    var termOrder = conj.order    

    val singleLiterals =
      (for (p <- predConj.positiveLits; if p.predicates subsetOf funPreds) yield new PseudoLiteral(List(), FunEquation(p))) ++
      (for (p <- predConj.positiveLits; if !(p.predicates subsetOf funPreds)) yield new PseudoLiteral(List(), PositiveLiteral(p))) ++    
    (for (p <- predConj.negativeLits; if !(p.predicates subsetOf funPreds)) yield new PseudoLiteral(List(), NegativeLiteral(p)))

    val funEqs =
      (for (p <- conj.predConj.positiveLits.iterator; if p.predicates subsetOf funPreds) yield FunEquation(p)).toList    

    // for (a <- predConj.positiveLits)
    //   dprintln("..." + a)

    // dprintln("\tpredConj: " + conj.predConj)
    // dprintln("\t\t" + conj.predConj.positiveLits)
    // dprintln("\t\t" + conj.predConj.negativeLits)
    // dprintln("\t\t" + conj.predConj.iterator)
    // dprintln("\tarithConj: " + conj.arithConj)
    // dprintln("\tneg: " + conj.negatedConjs)




    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, conj.arithConj.positiveEqs.size == 0)
    Debug.assertInt(ConnectionProver.AC, conj.arithConj.negativeEqs.size == 0)     
    Debug.assertInt(ConnectionProver.AC, conj.arithConj.inEqs.size == 0)
    Debug.assertInt(ConnectionProver.AC, conj.negatedConjs.length == 1 || singleLiterals.length == 1)
    //-END-ASSERTION-//////////////////////////////////////////////////////////

    dprintln("\tsingleLiterals: " + singleLiterals.mkString(","))

    val (pl, bo) = 
      if (!singleLiterals.isEmpty)
        (new PseudoClause(singleLiterals.toList), List())
      else
        disjunctionToClause(conj.negatedConjs(0))

    // Move all universals to the front
    val newBo = bo.filter(_._2) ++ bo.filter(!_._2)
    (pl, newBo)
  }

  def convertNegFunEq(funEq : Atom) : (FunEquation, NegEquation, BREUOrder) = {
    dprintln("convertNegFunEq(" + funEq + ")")
    val fun = funEq.pred

    // val res = funEq(funEq.length-1).lastTerm.constants.head

    val args = funEq.init
    dprintln("\targs: " + args.mkString(", "))

    val res = funEq.last
    dprintln("\tres: " + res)    

    val newTerm = new ConstantTerm("DUMMY_TERM_" + nextTerm)
    val newBREUOrder = List((newTerm, false))
    val newTermOrder = funEq.order.extend(newTerm)

    val negEqLC = LinearCombination(List((ap.basetypes.IdealInt.ONE, newTerm), (ap.basetypes.IdealInt.MINUS_ONE, res)), newTermOrder)
    dprintln("\tnegEqLC: " + negEqLC)

    nextTerm += 1
    val lc = LinearCombination(newTerm, newTermOrder)
    val newFunEq = FunEquation(Atom(fun, args ++ List(lc), newTermOrder))
    dprintln("\tnewFunEq: " + newFunEq)
    // val newEq = NegEquation(res.constants.head, newTerm)
    val (lhs, rhs, newEq) = eqTerms(negEqLC, newTermOrder)
    val eq = NegEquation(lhs, rhs)
    dprintln("\teq: " + eq)
    (newFunEq, eq, newBREUOrder)
  }

  def clauseWidth(conj : Conjunction) = conjToClause(fullInst(conj, "clauseWidth")._1)._1.length

  // TODO: Is this sound, ask Philipp!
  def isUnitClause(conj : Conjunction) : Boolean = conj.boundVariables.size == 0

  def extractConstants(conjs : List[Conjunction]) : BREUOrder = {
    (for (c <- conjs) yield c.constants).toSet.flatten.toList.map((_, false))
  }

  /*
   * Given a formula and a term ordering, and tries to prove it using connection tableuax
   */
  def solve(givenFor : Conjunction, termOrder : TermOrder) = ap.util.Timer.measure("Solve") {

    // Since the formula is in CNF, everything should be in the negated conjunctions
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ConnectionProver.AC, givenFor.predConj.size == 0 && givenFor.arithConj.isEmpty)
    //-END-ASSERTION-//////////////////////////////////////////////////////////

    // Instantiate quantifiers with rigid variables and make into CNF

    val quans = givenFor.quans
    val tmpConstants = for (i <- 0 until givenFor.quans.length) yield (new ConstantTerm("CONSTANT_" + i))
    val tmpOrder = givenFor.order.extend(tmpConstants)
    val closedFor = givenFor.instantiate(tmpConstants)(tmpOrder)
    val clauses = closedFor.negate.iterator.toList.reverse

    def printConj(conj : Conjunction) {
      println(conj)
      dprintln("\tpos: " + conj.predConj.positiveLits)
      dprintln("\tneg: " + conj.predConj.negativeLits)
      dprintln("\tnegConj: " + conj.negatedConjs)
    }

    // println("Input Clauses (non-intantiated): ")
    // for (c <- clauses)
    //   printConj(c)

    println("Input Clauses: ")
    for ((c, bo) <- clauses.map(x => conjToClause(fullInst(x, "conv")._1)))
      println("\t" + c + "  $  " + bo.mkString(","))

    var initBREUOrder = List() : BREUOrder
    val unitClauses : List[PseudoClause] =
      for (c <- clauses if isUnitClause(c)) yield {
        val (clause, tmpBREUOrder) = conjToClause(fullInst(c, "conv")._1)
        initBREUOrder ++= tmpBREUOrder
        clause
      }

    if (!unitClauses.isEmpty)
      println(unitClauses.map(_.toString).mkString("Unit Clauses:\n\t", "\n\t","\n"))



    // (false, Goal(List(givenFor), Set(), Vocabulary(termOrder), preSettings))


    def tryFirstClause(idx : Int, maxIterations : Int) :
        (Option[ConnectionTable], Boolean) = {

      val (firstClause, newTerms) = fullInst(clauses(idx), "base")


      println("\n//-----------------------------")      
      println("||Trying with initial clause: " + firstClause)
      val baseOrder = initBREUOrder ++ extractConstants(clauses) ++ List((new ConstantTerm("MIN"), false))
      println("|| baseOrder: " + baseOrder)
      println("|| newTerms: " + newTerms)
      println("\\-----------------------------")      

      // We have to extract all firstBREUOrder in the problem


      val unitNodes = unitClauses.map(_.head.nodes).flatten : List[Node]

      val (initClause, someBREUOrder) = conjToClause(firstClause)

      // TODO: This is not very elegant, but hopefully correct?
      val initOrder = (newTerms ++ someBREUOrder ++ baseOrder)

      val initTable  =
        new ConnectionTable(for (plit <- initClause.pseudoLiterals) yield {
          new ConnectionBranch(plit.nodes ++ unitClauses.map(_.head.nodes).flatten, ClosedStyle.Open, initOrder)
        }, preSettings)

      solveTable(initTable, clauses, maxIterations, 0, List())
    }



    var table = None : Option[ConnectionTable]

    var maxIteration = 2
    var maxReached = true

    while (table.isEmpty && maxReached) {
      var tryIdx = 0
      maxReached = false
      println("//-----------------------------")
      println("||  TRYING maxIteration: " + maxIteration)
      println("\\\\-----------------------------\n\n")

      // println(ap.util.Timer)
      // println("||")
      // println("|| safeSKIPs: " +safeSKIP)
      // println("||")

      while (table.isEmpty && tryIdx < clauses.length) {
        val (t, mr) = tryFirstClause(tryIdx, maxIteration)
        table = t
        maxReached |= mr
        tryIdx += 1
      }

      if (maxReached) {
        println("Increasing max iteration:")
        maxIteration *= 2
      }
    }

    println(ap.util.Timer)
    if (!table.isEmpty) {
      println("\n\n\n\tTable closed\n\n\n")
      val finalTable = table.get
      val finalMap = finalTable.unifyBranches()
      println("CLOSED TABLE:")
      // println("with order: " + finalOrder.mkString(", "))
      println(finalTable)
      println("Using: " + finalMap.get)
      (true, Goal(List(givenFor), Set(), Vocabulary(termOrder), preSettings))
    } else {
      println("Could not close table")
      (false, Goal(List(givenFor), Set(), Vocabulary(termOrder), preSettings))
    }
  }
}


