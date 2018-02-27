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
// Make NegFunEquation just Equation with polarity?
// Line 705 fix on geo118+1.p
// TODO: Fix terms vs order (BREUterms?)

package ap.connection;

import ap.terfor.{TermOrder, ConstantTerm}
import ap.terfor.conjunctions.{Conjunction, Quantifier}
import ap.terfor.preds.{Atom, PredConj}
import ap.terfor.arithconj.ArithConj
import ap.terfor.linearcombination.LinearCombination
import ap.proof.goal.Goal
import ap.util.{Debug, Timer}
import ap.parameters.{GoalSettings, Param}
import ap.proof.Vocabulary
import ap.connection.connection.{BREUOrder, OrderClause, OrderNode, clauseToString}

import scala.collection.mutable.{ListBuffer}

object ConnectionProver {
  // Not private?
  val AC = Debug.AC_CONNECTION_PROVER
}


class ConnectionProver(depthFirst : Boolean, preSettings : GoalSettings, strong : Boolean) {

  // How many of our closing-attempts could easily be ignored
  var safeSKIP = 0

  val DEBUG = true

  // TODO: How to make this nicer?
  var nextPredicate = 0
  var nextTerm = 0


  // Instantiate first level conj with new variables added to order with prefix
  def inst(conj : Conjunction, prefix : String, order : TermOrder) : (Conjunction, BREUOrder, TermOrder) = {
    var allCount = -1
    var exCount = -1

    val quants =
      for (q <- conj.quans) yield {
        q match { // 
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

    val newOrder = conj.order.extend(quants.map(_._1))
    (conj.instantiate(quants.map(_._1))(newOrder), quants.toList, newOrder)
  }


  // Fully instantiate conj with prefix
  def fullInst(conj : Conjunction, prefix : String) = {
    // Instantiate top-level
    val allTerms : ListBuffer[(ConstantTerm, Boolean)] = ListBuffer()

    val (newConj, nt, norder) = inst(conj, prefix, conj.order)
    allTerms ++= nt

    val retVal =
      if (newConj.negatedConjs.size == 1) {
        val disjunction = newConj.negatedConjs(0)
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
        Debug.assertInt(ConnectionProver.AC, disjunction.quans.length == 0)
        //-END-ASSERTION-//////////////////////////////////////////////////////////

        // Check all assumption-based formulas:
        var negOrder = norder
        val updatedNegConj =
          for (nc <- disjunction.negatedConjs) yield {
            val (newConj, nt, tmporder) = inst(nc, prefix + "_disj", negOrder)
            negOrder = tmporder
            allTerms ++= nt
            newConj
          }

        val tmp = disjunction.negatedConjs.update(updatedNegConj, negOrder)
        val finalDisjunction = disjunction.updateNegatedConjs(tmp)(negOrder)
        val tmp2 = newConj.negatedConjs.update(List(finalDisjunction), negOrder)
        val finalConj = newConj.updateNegatedConjs(tmp2)(negOrder)
        (finalConj, allTerms.toList.reverse, negOrder)
      } else {
        // TODO: This and above, really reverse?
        (newConj, allTerms.toList.reverse, norder)
      }

    retVal
  }



  def convertNegFunEquation(negFunEq : NegFunEquation) = {
    val pc = negFunEq.eq
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, pc.isLiteral && pc.positiveLits.length == 1)
    //-END-ASSERTION-//////////////////////////////////////////////////////////
    val atom = pc.positiveLits(0)
    val fun = atom.pred
    val args = atom.take(atom.length-1).map(x => x.lastTerm.constants.head)
    val res = atom(atom.length-1).lastTerm.constants.head
    (fun, args.toList, res)
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
  def tryStep(table : ConnectionTable, step : Int, branchIdx : Int, inputClauses : List[Conjunction], iteration : Int, disequalities : Seq[(ConstantTerm, ConstantTerm)]) : Option[ConnectionTable] = {
    val closedTable =
      if (step == 0) {
        Some(table.close(branchIdx, strong))
      } else ap.util.Timer.measure("Extending Table") {
        val (clause, idx) = findLiteral(inputClauses, step - 1)
        val (instClause, newOrder, _) = fullInst(clause, "branch_" + iteration)
        val orderClause = conjToClause(instClause, false)
        val extendedTable = table.extendBranch(branchIdx, orderClause, idx, newOrder)
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
   * Given a table 
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
    } else if (iteration <= maxIteration) {
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
    } else {
      throw new Exception("This case shouldn't happen...")
    }
  }

  def predToNodes(predConj : PredConj, negated : Boolean) : OrderClause = {
    val newNodes = ListBuffer() : ListBuffer[OrderNode]

    for (p <- predConj.iterator) {
      if ((p.predicates.size == 1) && (p.predicates subsetOf Param.FUNCTIONAL_PREDICATES(preSettings))) {
        if (negated) {
          // Convert to a funeq and a negeq
          val (_, _, res2) = convertNegFunEquation(NegFunEquation(p))

          val atom = p.positiveLits(0)
          val fun = atom.pred
          val args = atom.take(atom.length-1)
          val res = atom(atom.length-1)
          val newTerm = new ConstantTerm("DUMMY_TERM_" + nextTerm)
          val newOrder = List((newTerm, false))
          val no = p.order.extend(newTerm)

          nextTerm += 1
          val lc = LinearCombination(newTerm, no)
          val newFunEq = Atom(fun, args ++ List(lc), no)
          val newEq = NegEquation(res2, newTerm)

          newNodes += ((List(newEq, FunEquation(PredConj(List(newFunEq), List(), no))), newOrder))

        } else {
          newNodes += ((List(FunEquation(p)) : List[Node], List() : BREUOrder))
        }
      } else if (p.predicates.size == 1) {
        if (negated)
          newNodes += ((List(Literal(!p)), List()))
        else
          newNodes += ((List(Literal(p)), List()))
      } else {
        throw new Exception("More than one predicate in predConj!")
      }
    }

    if (newNodes.isEmpty) {
      List()
    } else {
      // TODO: Not sure about this one
      if (negated) {
        newNodes.toList
      } else {
        // TODO: Do we have to place the orders in some kind of order (no pun intended)
        val newEqs : List[Node] = for (n <- newNodes.map(_._1).flatten.toList if !n.isLiteral) yield n
        val newLits : List[Node] = for (n <- newNodes.map(_._1).flatten.toList if n.isLiteral) yield n
        val newOrder : BREUOrder = newNodes.map(_._2).flatten.toList
        List((newLits ++ newEqs, newOrder))
      }
    }
  }

  // Can only be used on instatiated clauses!
  def arithToNodes(arithConj : ArithConj, negated : Boolean) : OrderClause = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, arithConj.inEqs.size == 0 && arithConj.positiveEqs.size == 0)
    //-END-ASSERTION-//////////////////////////////////////////////////////////
    if (arithConj.isTrue) { 
      List()
    } else {
      val nodes : OrderClause =
        for (eq <- arithConj.negativeEqs.toList) yield {
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
            case (ct1 : ConstantTerm, ct2 : ConstantTerm) =>
              if (negated)
                (List(Equation(ct1, ct2)), List()) : OrderNode
              else
                (List(NegEquation(ct1, ct2)), List()) : OrderNode
            case _ =>
              throw new Exception("Non ConstantTerm in arithConj.negativeEqs (" + t1 + " : " + t1.getClass + ") (" + t2 + " : " + t2.getClass + ")")
          }
        }
      nodes
    }
  }

  def conjToList(conj : Conjunction, negated : Boolean) : List[OrderNode] = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, conj.negatedConjs.length == 0)
    //-END-ASSERTION-//////////////////////////////////////////////////////////

    val predLiterals = predToNodes(conj.predConj, negated)
    val eqLiterals = arithToNodes(conj.arithConj, negated)
    predLiterals ++ eqLiterals
  }


  def subConjToClause(conj : Conjunction, negated : Boolean) : List[OrderNode] = {
    val predLiterals = predToNodes(conj.predConj, negated)
    val eqLiterals = arithToNodes(conj.arithConj, negated)
    val singleLiterals = (predLiterals ++ eqLiterals)
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, conj.negatedConjs.length == 0 || conj.negatedConjs.length == 1)
    //-END-ASSERTION-//////////////////////////////////////////////////////////
    if (conj.negatedConjs.isEmpty)
      singleLiterals
    else
      singleLiterals ++ conjToList(conj.negatedConjs.head, !negated)
  }

  def conjToClause(conj : Conjunction, negated : Boolean) : OrderClause = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, conj.negatedConjs.length == 0 || conj.negatedConjs.length == 1)
    //-END-ASSERTION-//////////////////////////////////////////////////////////
    val predLiterals = predToNodes(conj.predConj, negated)
    val eqLiterals = arithToNodes(conj.arithConj, negated)

    // The negative literals should be returned as one List of list of nodes
    val negLiterals =
      if (conj.negatedConjs.length == 0)
        List()
      else
        subConjToClause(conj.negatedConjs(0), !negated)

    // Now we combine both the top-level literals as well as the multi-part literals
    predLiterals ++ eqLiterals ++ negLiterals
  }

  def clauseWidth(conj : Conjunction) = conjToClause(fullInst(conj, "clauseWidth")._1, false).length

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

    if (DEBUG) {
      println("Converting to CNF")
      println("\t" + givenFor)
    }

    // Instantiate quantifiers with rigid variables and make into CNF
    val quans = givenFor.quans
    val tmpConstants = for (i <- 0 until givenFor.quans.length) yield (new ConstantTerm("CONSTANT_" + i))
    val tmpOrder = givenFor.order.extend(tmpConstants)
    val closedFor = givenFor.instantiate(tmpConstants)(tmpOrder)
    val negQuans = closedFor.negate.quans
    val inputClauses = closedFor.negate.iterator.toList.reverse

    if (DEBUG) {
      println("\t--------")
      for (c <- inputClauses)
        println("\t" + c + " => " + (conjToClause(fullInst(c, "conv")._1, false)))
    }

    val clauses = for (c <- inputClauses) yield { Conjunction.quantify(negQuans, c, c.order) }

    println("Input Clauses: ")
    for (c <- inputClauses) {
      println("\t" + c)
      println("\t\t" + clauseToString((conjToClause(fullInst(c, "conv")._1, false))))
    }

    val unitInst = for (c <- clauses if isUnitClause(c)) yield conjToClause(fullInst(c, "conv")._1, false)
    val unitClauses = unitInst.map(_(0))

    println("Unit Clauses:\n " + unitClauses.mkString("\t", "\n\t", "\n"))

    val baseOrder = extractConstants(clauses) ++ List((new ConstantTerm("MIN"), false))
    println("Base Order: " + baseOrder)



    def tryFirstClause(idx : Int, maxIterations : Int) :
        (Option[ConnectionTable], Boolean) = {

      val (firstClause, terms, newOrder) = fullInst(clauses(idx), "base")

      println("||\n||Trying with initial clause: " + firstClause)

      // We have to extract all terms in the problem
      val initOrder = (terms ++ baseOrder)
      // TODO: Not so nice...

      val unitNodes = unitClauses.map(_._1).flatten : List[Node]
      // TODO: initOrder2!?, come on ...
      val initTable  =
        new ConnectionTable(for ((nodes, extraOrder) <- conjToClause(firstClause, false)) yield {
          new ConnectionBranch(nodes ++ unitNodes, ClosedStyle.Open, initOrder ++  extraOrder)
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
      (true, Goal(List(closedFor), Set(), Vocabulary(termOrder), preSettings))
    } else {
      println("Could not close table")
      (false, Goal(List(closedFor), Set(), Vocabulary(termOrder), preSettings))
    }
  }
}
