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
import ap.terfor.preds.{Atom, PredConj}
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


class ConnectionProver(depthFirst : Boolean, preSettings : GoalSettings, strong : Boolean) {
  // How many of our closing-attempts could easily be ignored
  var safeSKIP = 0

  val DEBUG = true

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
  def fullInst(conj : Conjunction, prefix : String) =
    instantiateAux(conj, prefix, conj.order)

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
    val closedTable =
      if (step == 0) {
        Some(table.close(branchIdx, strong))
      } else ap.util.Timer.measure("Extending Table") {
        val (clause, idx) = findLiteral(inputClauses, step - 1)
        val (instClause, newOrder, _) = fullInst(clause, "branch_" + iteration)
        val pseudoClause = conjToClause(instClause)
        val extendedTable = table.extendBranch(branchIdx, pseudoClause, idx, newOrder)
        extendedTable.closeSafe(branchIdx, strong)
      }

    if (closedTable.isEmpty) {
      safeSKIP += 1
      None
    } else ap.util.Timer.measure("Checking closable") {
      if (closedTable.get.closable(disequalities)) {
        Some(closedTable.get)
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
      (Some(table), false)
    } else if (table.openBranches > maxIteration - iteration) {
      // We can't close n branches with <n iterations
      (None, true)
    } else {
      // Let's try one more step...

      // val (extendingBranch, extendingBranchIdx) = table.firstOpen
      val (branch, branchIdx) = table.shortestOpen

      // TODO: Any way of making branch a val and branchStep a var?
      println("//--------- " + iteration + " -------------")
      println("|| Branches: (" + table.width + ") extending (" + branchIdx + ")")
      println((for (l <- table.toString.split("\n").toList) yield ("|| " + l)).mkString("\n"))
      println("Disequalities: " + disequalities.mkString(", "))

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
          val (t, mr) = solveTable(res.get, inputClauses, maxIteration, iteration + 1, res.get.diseqPairs.toList ++ disequalities)
          if (!t.isEmpty)
            return (t, mr)
          maxReached |= mr
        }
        step += 1
      }

      println("\\\\---------     -------------")
      (None, maxReached)
    }
  }


  def predToPseudoLiteral(p : PredConj, termOrder : TermOrder, negated : Boolean = false) : (PseudoLiteral, BREUOrder, TermOrder)= {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, p.positiveLits.length == 1 || p.negativeLits.length == 1)
    //-END-ASSERTION-//////////////////////////////////////////////////////////
    
    if (p.positiveLits.length > 0) {
      val atom = p.positiveLits(0)
      val fun = atom.pred
      val args = atom.take(atom.length-1)

      val res = atom(atom.length-1).lastTerm.constants.head
      val newTerm = new ConstantTerm("DUMMY_TERM_" + nextTerm)
      val newBREUOrder = List((newTerm, false))
      val newTermOrder = termOrder.extend(newTerm)

      nextTerm += 1
      val lc = LinearCombination(newTerm, newTermOrder)
      val newFunEq = FunEquation(PredConj(List(Atom(fun, args ++ List(lc), newTermOrder)), List(), newTermOrder))
      val newEq =
        if (negated)
          NegEquation(res, newTerm)
        else
          Equation(res, newTerm)
      val lit = new PseudoLiteral(List(newFunEq), newEq)
      (lit, newBREUOrder, newTermOrder)
    } else {
      val atom = p.negativeLits(0)
      val fun = atom.pred
      val args = atom.take(atom.length-1)

      val res = atom(atom.length-1).lastTerm.constants.head
      val newTerm = new ConstantTerm("DUMMY_TERM_" + nextTerm)
      val newBREUOrder = List((newTerm, false))
      val newTermOrder = termOrder.extend(newTerm)

      nextTerm += 1
      val lc = LinearCombination(newTerm, newTermOrder)
      val newFunEq = FunEquation(PredConj(List(Atom(fun, args ++ List(lc), newTermOrder)), List(), newTermOrder))
      val newEq =
        if (negated)
          Equation(res, newTerm)
        else
          NegEquation(res, newTerm)
      val lit = new PseudoLiteral(List(newFunEq), newEq)
      (lit, newBREUOrder, newTermOrder)
    }
  }

  // def predToNodes(predConj : PredConj, negated : Boolean = false) : (List[PseudoLiteral], BREUOrder, TermOrder) = {
  //   var breuOrder = List() : BREUOrder
  //   var termOrder = predConj.order
  //   println("predToNodes(" + predConj + ")")
  //   for (p <- predConj.iterator)
  //     println("\t" + p)
  //   val newLits = 
  //     for (p <- predConj.iterator) yield {
  //       // Function!
  //       val isFunction = p.predicates subsetOf Param.FUNCTIONAL_PREDICATES(preSettings)
  //       val (newLit, newBREUOrder, newTermOrder) =
  //         (isFunction, negated) match {
  //           case (true, negated) => predToPseudoLiteral(p, termOrder, negated)
  //           case (false, true) => (new PseudoLiteral(List(), Literal(!p)), List(), termOrder)
  //           case (false, false) =>(new PseudoLiteral(List(), Literal(p)), List(), termOrder)
  //         }
  //       breuOrder = newBREUOrder ++ breuOrder
  //       termOrder = newTermOrder
  //       newLit
  //     }

  //   (newLits.toList, breuOrder, termOrder)

  //     // // TODO: Not sure about this one
  //     // if (negated) {
  //     //   newNodes.toList
  //     // } else {
  //     //   // TODO: Do we have to place the orders in some kind of order (no pun intended)
  //     //   val newEqs : List[Node] = for (n <- newNodes.map(_._1).flatten.toList if !n.isLiteral) yield n
  //     //   val newLits : List[Node] = for (n <- newNodes.map(_._1).flatten.toList if n.isLiteral) yield n
  //     //   val newOrder : BREUOrder = newNodes.map(_._2).flatten.toList
  //     //   List((newLits ++ newEqs, newOrder))
  // }

  /**
    * Given a (Princess) ArithConj returns it converted to a list of PseudoLiterals
    * 
    * PRE: arithConj must instantiated
    * 
    * If negated is true, then all equations will be converted to negative equations
    */
  // Can only be used on instatiated clauses!
  // def arithToNodes(arithConj : ArithConj, negated : Boolean = false) : List[PseudoLiteral] = {
  //   //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
  //   Debug.assertInt(ConnectionProver.AC, arithConj.inEqs.size == 0 && arithConj.positiveEqs.size == 0)
  //   //-END-ASSERTION-//////////////////////////////////////////////////////////
  //   if (arithConj.isTrue) { 
  //     List()
  //   } else {
  //     for (eq <- arithConj.negativeEqs.toList) yield {
  //       val pairs = eq.pairSeq.toList
  //       //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
  //       Debug.assertInt(ConnectionProver.AC, pairs.length == 2)
  //       //-END-ASSERTION-//////////////////////////////////////////////////////////
  //       val (c1, t1) = pairs(0)
  //       val (c2, t2) = pairs(1)
  //       //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
  //       Debug.assertInt(ConnectionProver.AC, (c1.intValue == 1 && c2.intValue == -1) || (c1.intValue == -1 && c2.intValue == 1) )
  //       //-END-ASSERTION-//////////////////////////////////////////////////////////
  //         (t1, t2) match {
  //         case (ct1 : ConstantTerm, ct2 : ConstantTerm) =>
  //           if (negated)
  //             new PseudoLiteral(List(), Equation(ct1, ct2))
  //           else
  //             new PseudoLiteral(List(), NegEquation(ct1, ct2))
  //         case _ =>
  //           throw new Exception("Non ConstantTerm in arithConj.negativeEqs (" + t1 + " : " + t1.getClass + ") (" + t2 + " : " + t2.getClass + ")")
  //       }
  //     }
  //   }
  // }


  // Sometimes the pred can be empty??
  def negNegConjToLiteral(conj : Conjunction) : PseudoLiteral = {
    
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, conj.arithConj.inEqs.size == 0 && conj.arithConj.positiveEqs.size == 0)
    Debug.assertInt(ConnectionProver.AC, conj.negatedConjs.size == 0)
    //-END-ASSERTION-//////////////////////////////////////////////////////////

    var breuOrder = List() : BREUOrder
    var termOrder = conj.order

    var funs = ListBuffer() : ListBuffer[FunEquation]
    var pred = None : Option[Node]


    for (p <- conj.predConj.iterator) {
      // Function!
      if (p.predicates subsetOf Param.FUNCTIONAL_PREDICATES(preSettings)) {
        // val (newLit, newBREUOrder, newTermOrder) = predToPseudoLiteral(p, termOrder)
        // breuOrder = newBREUOrder ++ breuOrder
        // termOrder = newTermOrder
        funs += FunEquation(p)
      } else {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
        Debug.assertInt(ConnectionProver.AC, !pred.isDefined)
        //-END-ASSERTION-//////////////////////////////////////////////////////////
        pred = Some(Literal(p))
      }
    }

    if (!conj.arithConj.isTrue) {
      for (eq <- conj.arithConj.negativeEqs.toList) {
        val pairs = eq.pairSeq.toList
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
        Debug.assertInt(ConnectionProver.AC, pairs.length == 2)
        //-END-ASSERTION-//////////////////////////////////////////////////////////
        val (c1, t1) = pairs(0)
        val (c2, t2) = pairs(1)
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
        Debug.assertInt(ConnectionProver.AC, (c1.intValue == 1 && c2.intValue == -1) || (c1.intValue == -1 && c2.intValue == 1) )
        //-END-ASSERTION-//////////////////////////////////////////////////////////
          (t1, t2) match {
          case (ct1 : ConstantTerm, ct2 : ConstantTerm) => {
            //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
            Debug.assertInt(ConnectionProver.AC, !pred.isDefined)
            //-END-ASSERTION-//////////////////////////////////////////////////////////
            pred = Some(NegEquation(ct1, ct2))
          }
          case _ => throw new Exception("Non ConstantTerm in arithConj.negativeEqs (" + t1 + " : " + t1.getClass + ") (" + t2 + " : " + t2.getClass + ")")
        }
      }
    }

    pred match {
      case None => new PseudoLiteral(funs.toList, True)
      case Some(p) => new PseudoLiteral(funs.toList, p)
    }
  }

  def negConjToClause(conj : Conjunction) : PseudoClause = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, conj.arithConj.inEqs.size == 0 && conj.arithConj.positiveEqs.size == 0)
    Debug.assertInt(ConnectionProver.AC, conj.negatedConjs.length == 0 || conj.negatedConjs.length == 1)    
    //-END-ASSERTION-//////////////////////////////////////////////////////////

    var breuOrder = List() : BREUOrder
    var termOrder = conj.order

    val predicateLiterals = 
      for (p <- conj.predConj.iterator) yield {
        // Function!
        if (p.predicates subsetOf Param.FUNCTIONAL_PREDICATES(preSettings)) {
          val (newLit, newBREUOrder, newTermOrder) = predToPseudoLiteral(p, termOrder, true)
          breuOrder = newBREUOrder ++ breuOrder
          termOrder = newTermOrder
          newLit
        } else {
          new PseudoLiteral(List(), Literal(!p))
        }
      }

    val arithLiterals = 
    if (!conj.arithConj.isTrue) { 
      for (eq <- conj.arithConj.negativeEqs.toList) yield {
        val pairs = eq.pairSeq.toList
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
        Debug.assertInt(ConnectionProver.AC, pairs.length == 2)
        //-END-ASSERTION-//////////////////////////////////////////////////////////
        val (c1, t1) = pairs(0)
        val (c2, t2) = pairs(1)
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
        Debug.assertInt(ConnectionProver.AC, (c1.intValue == 1 && c2.intValue == -1) || (c1.intValue == -1 && c2.intValue == 1) )
        //-END-ASSERTION-//////////////////////////////////////////////////////////
          (t1, t2) match {
          case (ct1 : ConstantTerm, ct2 : ConstantTerm) => new PseudoLiteral(List(), Equation(ct1, ct2))
          case _ => throw new Exception("Non ConstantTerm in arithConj.negativeEqs (" + t1 + " : " + t1.getClass + ") (" + t2 + " : " + t2.getClass + ")")
        }
      }
    } else {
      List()
    }

    val negLiterals =
      if (conj.negatedConjs.length > 0)
        List(negNegConjToLiteral(conj.negatedConjs(0)))
      else
        List()

    new PseudoClause((predicateLiterals ++ arithLiterals ++ negLiterals).toList)
  }


  // def negConjToPseudoLiteral(conj : Conjunction) : PseudoLiteral = {
  //   i()
  //   p("negConj...(" + conj + ")")
  //   p("\tnegSize: " + conj.negatedConjs.size)
  //   p("\tpredConj: " + conj.predConj)
  //   p("\tarithConj: " + conj.arithConj)
  //   d()

  //   val predicateLiterals  = 
  //     for (p <- conj.predConj.iterator) yield {
  //       if (p.predicates subsetOf Param.FUNCTIONAL_PREDICATES(preSettings)) {
  //         val (newLit, newBREUOrder, newTermOrder) = predToPseudoLiteral(p, conj.order, true)
  //         // breuOrder = newBREUOrder ++ breuOrder
  //         // termOrder = newTermOrder
  //         newLit
  //       } else {
  //         new PseudoLiteral(List(), Literal(p))
  //       }
  //     }

  //   val arithLiterals : List[PseudoLiteral] = 
  //     if (!conj.arithConj.isTrue) {
  //       for (eq <- conj.arithConj.negativeEqs.toList) yield {
  //         val pairs = eq.pairSeq.toList
  //         //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
  //         Debug.assertInt(ConnectionProver.AC, pairs.length == 2)
  //         //-END-ASSERTION-//////////////////////////////////////////////////////////
  //         val (c1, t1) = pairs(0)
  //         val (c2, t2) = pairs(1)
  //         //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
  //         Debug.assertInt(ConnectionProver.AC, (c1.intValue == 1 && c2.intValue == -1) || (c1.intValue == -1 && c2.intValue == 1) )
  //         //-END-ASSERTION-//////////////////////////////////////////////////////////
  //           (t1, t2) match {
  //           case (ct1 : ConstantTerm, ct2 : ConstantTerm) => new PseudoLiteral(List(), Equation(ct1, ct2))
  //           case _ => throw new Exception("Non ConstantTerm in arithConj.negativeEqs (" + t1 + " : " + t1.getClass + ") (" + t2 + " : " + t2.getClass + ")")
  //         }
  //       }
  //     } else {
  //       List()
  //     }


  //   //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
  //   Debug.assertInt(ConnectionProver.AC, predicateLiterals.length + arithLiterals.length == 1)    
  //   //-END-ASSERTION-//////////////////////////////////////////////////////////

  //   (predicateLiterals ++ arithLiterals).toList.head
  // }

  /**
    * Converts from (internal Princess) Conjunction to an PseudoClause
    * 	...EX EX (f(_1, _0) & R(_1) & ! EX (!R(_0)))
    */
  def conjToClause(conj : Conjunction) : PseudoClause = {
    // Two possibilities, either it is a single predicate or arithmetic literal
    // Or it is a disjunction

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, conj.arithConj.inEqs.size == 0 && conj.arithConj.positiveEqs.size == 0)
    Debug.assertInt(ConnectionProver.AC, conj.arithConj.inEqs.size == 0 && conj.arithConj.positiveEqs.size == 0)        
    //-END-ASSERTION-//////////////////////////////////////////////////////////

    var breuOrder = List() : BREUOrder
    var termOrder = conj.order

    val funs = ListBuffer() : ListBuffer[FunEquation]
    var pred = None : Option[Node]

    val predicateLiterals = 
      for (p <- conj.predConj.iterator) yield {
        // Function!
        if (p.predicates subsetOf Param.FUNCTIONAL_PREDICATES(preSettings)) {
          val (newLit, newBREUOrder, newTermOrder) = predToPseudoLiteral(p, termOrder)
          breuOrder = newBREUOrder ++ breuOrder
          termOrder = newTermOrder
          newLit
        } else {
          new PseudoLiteral(List(), Literal(p))
        }
      }

    val arithLiterals = 
    if (!conj.arithConj.isTrue) { 
      for (eq <- conj.arithConj.negativeEqs.toList) yield {
        val pairs = eq.pairSeq.toList
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
        Debug.assertInt(ConnectionProver.AC, pairs.length == 2)
        Debug.assertInt(ConnectionProver.AC, !pred.isDefined)        
        //-END-ASSERTION-//////////////////////////////////////////////////////////
        val (c1, t1) = pairs(0)
        val (c2, t2) = pairs(1)
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
        Debug.assertInt(ConnectionProver.AC, (c1.intValue == 1 && c2.intValue == -1) || (c1.intValue == -1 && c2.intValue == 1) )
        //-END-ASSERTION-//////////////////////////////////////////////////////////
          (t1, t2) match {
          case (ct1 : ConstantTerm, ct2 : ConstantTerm) => new PseudoLiteral(List(), NegEquation(ct1, ct2))
          case _ => throw new Exception("Non ConstantTerm in arithConj.negativeEqs (" + t1 + " : " + t1.getClass + ") (" + t2 + " : " + t2.getClass + ")")
        }
      }
    } else {
      List()
    }

    if (predicateLiterals.isEmpty && arithLiterals.isEmpty)
      negConjToClause(conj.negatedConjs(0))
    else
      new PseudoClause((predicateLiterals ++ arithLiterals ).toList)
  }

  def clauseWidth(conj : Conjunction) = conjToClause(fullInst(conj, "clauseWidth")._1).length

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
    // val negQuans = closedFor.negate.quans
    // val clauses = closedFor.negate.iterator.toList.reverse
    val clauses = closedFor.negate.iterator.toList.reverse

    // val clauses = for (c <- inputClauses) yield { Conjunction.quantify(negQuans, c, c.order) }
    // val clauses = closedFor.negate

    println("Input Clauses: ")
    for (c <- clauses) {
      println("\t" + c)
    }

    val conjs = clauses.map(x => conjToClause(fullInst(x, "conv")._1))

    println("Input Conjs: ")
    for (c <- conjs) {
      println("\t" + c)
      // println("\t\t" + clauseToString((conjToClause(fullInst(c, "conv")._1))))
    }    



    val unitClauses : List[PseudoClause] =
      for (c <- clauses if isUnitClause(c)) yield conjToClause(fullInst(c, "conv")._1)

    println("Unit Clauses:\n " + unitClauses.mkString("\t", "\n\t", "\n"))

    val baseOrder = extractConstants(clauses) ++ List((new ConstantTerm("MIN"), false))
    println("Base Order: " + baseOrder)

      (false, Goal(List(givenFor), Set(), Vocabulary(termOrder), preSettings))    


    def tryFirstClause(idx : Int, maxIterations : Int) :
        (Option[ConnectionTable], Boolean) = {

      val (firstClause, terms, newOrder) = fullInst(clauses(idx), "base")

      println("||\n||Trying with initial clause: " + firstClause)

      // We have to extract all terms in the problem
      val initOrder = (terms ++ baseOrder)

      val unitNodes = unitClauses.map(_.head.nodes).flatten : List[Node]

      val initTable  =
        new ConnectionTable(for (plit <- conjToClause(firstClause).pseudoLiterals) yield {
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
      println(ap.util.Timer)
      println("||")
      println("|| safeSKIPs: " +safeSKIP)
      println("||")
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
