//
// Todo:
// 


// Make NegFunEquation just Equation with polarity?
// Line 705 fix on geo118+1.p
// TODO: Fix terms vs order (BREUterms?)


//
// CURRENT:
// Fix finding all closing pairs on a branch!
//
// Remove STEP
// Change tryStep to just adding one clause and then close
// Make function that searches for all structuralClosable nodes/pairs
// Make branch to breu find all nodes/pairs and make a disjunctive goal

/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2016 Peter Backeman <peter.backeman@it.uu.se>
 * Copyright (C) 2009-2015 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

package ap.connection;

import ap.terfor.{TermOrder, ConstantTerm}
import ap.terfor.conjunctions.{Conjunction, Quantifier}
import ap.terfor.preds.{Atom, PredConj}
import ap.terfor.arithconj.ArithConj
import ap.terfor.linearcombination.LinearCombination
import ap.proof.goal.Goal
import ap.util.Debug
import ap.parameters.{GoalSettings, Param}
import ap.proof.Vocabulary
import ap.connection.connection.{BREUOrder, OrderClause, OrderNode, clauseToString}

import scala.collection.mutable.{ListBuffer}

object ConnectionProver {
  // Not private?
  val AC = Debug.AC_CONNECTION_PROVER
}
class ConnectionProver(depthFirst : Boolean, preSettings : GoalSettings) {

  // TODO: How to make this nicer?
  var nextPredicate = 0
  var nextTerm = 0

  // Instantiate first level conj with new variables added to order with prefix
  // DONE
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

    val newOrder = conj.order.extend(quants.map(_._1))
    (conj.instantiate(quants.map(_._1))(newOrder), quants.toList, newOrder)
  }


  // Fully instantiate conj with prefix
  // DONE
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
        (finalConj, allTerms.toList, negOrder)
      } else {
        (newConj, allTerms.toList, norder)
      }

    // println("fullInst(" + conj + ") => " + retVal)
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

  // DONE
  def findStatement(inputClauses : List[Conjunction], step : Int) :
      (Conjunction, Int) = {
    if (step >= clauseWidth(inputClauses.head))
      findStatement(inputClauses.tail, step - clauseWidth(inputClauses.head))
    else
      (inputClauses.head, step)
  }

  var maxDepthReached = false
  var maxWidthReached = false

  def solveTable(
    table : ConnectionTable,
    inputClauses : List[Conjunction],
    maxDepth : Int,
    maxWidth : Int,
    iteration : Int) :
      Option[ConnectionTable] = {



    if (!table.isOpen)
      return Some(table)

    val (extendingBranch, extendingBranchIdx) = table.firstOpen
    var branch = extendingBranch.get
    val branchIdx = extendingBranchIdx
    val branchAtom = branch(0)

    // If branch is too long, stop
    if (branch.depth > maxDepth) {
      // println("|| MAX DEPTH REACHED")
      maxDepthReached = true
      return None
    }

    if (table.width > maxWidth) {
      // println("|| MAX WIDTH REACHED")
      maxWidthReached = true
      return None
    }

    // println("|| Current terms:")
    // println("||\t" + terms)

    // Pick a branch -- Always pick first open branch
    // TODO: Any way of making branch a val and branchStep a var?




    println("//-------------------------")
    println("|| Starting recursive iteration " + iteration)
    println("|| Branches: (" + table.branches.length + ")")
    println(table)
    println("|| Extending branch (" + branchIdx + ") ")



    // STEP 0: Try closing as-is
    // STEP 1+: Where (x, y) is input clause x with literal y:
    //          try (0,0), (0,1), ... (1,0) ...
    def tryStep(step : Int) : Option[ConnectionTable] = {
      val closedTable = 
        if (step == 0) {
          table.close(branchIdx)
        } else {
          // Try unifying with input clause, first we try first clause, first statement,
          // then first clause, second statement, ...
          val (clause, idx) = findStatement(inputClauses, step - 1)
          val (instClause, newOrder, _) = fullInst(clause, "branch_" + iteration)

          // TODO: This should not be here, negatedConjs should probably be used somewhere else...
          val orderClause = conjToClause(instClause, false)
          val extendedTable = table.extendBranch(branchIdx, orderClause, idx, newOrder)

          extendedTable.close(branchIdx)
        }

      if (closedTable.closable) {
        Some(closedTable)
      } else {
        None
      }
    }

    // We use the branchStep to decide where to search for the new candidate
    val maxStep = (inputClauses.map(clauseWidth(_)).sum)
    var branchStep = 0

    // TODO: Should this be <=?
    while (branchStep <= maxStep) {
      val res = tryStep(branchStep)
      if (branchStep == 0) {
        if (res.isEmpty)
          println("Trying close table right away, but failed")
        else
          println("Trying close table right away, success!")
      }
      if (!res.isEmpty) {
        val rec = solveTable(res.get, inputClauses, maxDepth, maxWidth, iteration + 1)
        if (!rec.isEmpty)
          return rec
      } 
      branchStep += 1
    }

    println("|| No applicable formula found...")
    println("|| Couldn't close table: ")
    println(table)
    println("\n\n\n")
    None
  }

  def predToNodes(predConj : PredConj, negated : Boolean) : OrderClause = {
    // println("predToNodes(" + predConj + ", " + negated + ")")
    
    val newNodes = ListBuffer() : ListBuffer[OrderNode]

    for (p <- predConj.iterator) {
      if ((p.predicates.size == 1) && (p.predicates subsetOf Param.FUNCTIONAL_PREDICATES(preSettings))) {
        if (negated) {
          // Convert to a funeq and a negeq
          val (_, _, res2) = convertNegFunEquation(NegFunEquation(p))
          // println("fun: " + fun)
          // println("args: " + args)
          // println("res: " + res)
          // funEqs += NegFunEquation(p)

          val pc = p
          val atom = pc.positiveLits(0)
          val fun = atom.pred
          val args = atom.take(atom.length-1)
          val res = atom(atom.length-1)
          val newTerm = new ConstantTerm("DUMMY_TERM_" + nextTerm)
          val newOrder = List((newTerm, false))
          val no = p.order.extend(newTerm)

          nextTerm += 1
          val lc = LinearCombination(newTerm, no)
          val newFunEq = Atom(fun, args ++ List(lc), no)
          // println("Converting " + p + " to:")
          // println("\tnewFunEq: " + newFunEq)

          val newEq = NegEquation(res2, newTerm)
          // println("\tnewEq = " + newEq)	ALL (! (!R(_0) & ! EX (f(_1, _0) & R(_0)))) => List(List(Literal(R(convALL0))), List(FunEquation(f(convALL0, conv_disjEX0))), List(Literal(R(conv_disjEX0))))

          // TODO: Fix this!
          val asd1 : List[Node] = List(newEq, FunEquation(PredConj(List(newFunEq), List(), no)))
          val asd2 : BREUOrder = newOrder
          val asd3 : OrderNode = (asd1, asd2)
          newNodes += asd3

        } else {
          val asd1 = List(FunEquation(p)) : List[Node]
          val asd2 = List() : BREUOrder
          newNodes += ((asd1, asd2) )
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

    val finalNodes = 
      if (newNodes.isEmpty) {
        List()
      } else {
        // TODO: Not sure about this one
        if (negated) {
          newNodes.toList
        } else { 
          // TODO: Do we have to place the orders in some kind of order (no pun intended)
          val newEq : List[Node] = for (n <- newNodes.map(_._1).flatten.toList if n.isEquation) yield n
          val newLits : List[Node] = for (n <- newNodes.map(_._1).flatten.toList if n.isLiteral) yield n
          val newOrder : BREUOrder = newNodes.map(_._2).flatten.toList
          List((newLits ++ newEq, newOrder))
        }
      }
    // println("\t" + finalNodes)
    finalNodes
  }

  // Can only be used on instatiated clauses!
  def arithToNodes(arithConj : ArithConj, negated : Boolean) : OrderClause = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, arithConj.inEqs.size == 0 && arithConj.positiveEqs.size == 0)
    //-END-ASSERTION-//////////////////////////////////////////////////////////
    if (arithConj.isTrue) { 
      List()
    } else {
      // println("arithToLiteral(" + arithConj + ")")
      val nodes : OrderClause =
        for (eq <- arithConj.negativeEqs.toList) yield {
          // println("\t" + eq)
          val pairs = eq.pairSeq.toList
          //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
          Debug.assertInt(ConnectionProver.AC, pairs.length == 2)
          //-END-ASSERTION-//////////////////////////////////////////////////////////
          val (c1, t1) = pairs(0)
          val (c2, t2) = pairs(1)
          // println("\t\t" + (c1, t1) + " ... " + (c2, t2))
          //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
          Debug.assertInt(ConnectionProver.AC, (c1.intValue == 1 && c2.intValue == -1) || (c1.intValue == -1 && c2.intValue == 1) )
          //-END-ASSERTION-//////////////////////////////////////////////////////////
          // println(arithConj + " => " + t1 + " != " + t2)
          // println("t1: " + t1 + " (" + t1.getClass + ")")
          // println("t2: " + t2 + " (" + t2.getClass + ")")
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
    // println("subConjToClause(" + conj + ", " + negated + ")")
    val predLiterals = predToNodes(conj.predConj, negated)
    val eqLiterals = arithToNodes(conj.arithConj, negated)
    val singleLiterals = (predLiterals ++ eqLiterals)
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, conj.negatedConjs.length == 0 || conj.negatedConjs.length == 1)
    //-END-ASSERTION-//////////////////////////////////////////////////////////
    // println("\tpredLiterals: " + predLiterals)
    // println("\teqLiterals: " + eqLiterals)
    // println("\tconj.negatedConjs: " + conj.negatedConjs)
    if (conj.negatedConjs.isEmpty) {
      // Only one literals
      singleLiterals
    } else {
      val negLiterals = conjToList(conj.negatedConjs.head, !negated)
      // println("\tnegLiterals: " + negLiterals)
      singleLiterals ++ negLiterals
    }
  }

  def conjToClause(conj : Conjunction, negated : Boolean) : OrderClause = {
    // println("conjToClause(" + conj + ", " + negated + ")")
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, conj.negatedConjs.length == 0 || conj.negatedConjs.length == 1)
    //-END-ASSERTION-//////////////////////////////////////////////////////////

    // println("predConj: " + conj.predConj)
    val predLiterals = predToNodes(conj.predConj, negated)
    val eqLiterals = arithToNodes(conj.arithConj, negated)
    // println("\tpredLiterals: " + predLiterals)
    // println("\tarithLiters: " + eqLiterals)

    // The negative literals should be returned as one List of list of nodes
    val negLiterals =
      if (conj.negatedConjs.length == 0)
        List()
      else
        subConjToClause(conj.negatedConjs(0), !negated)

    // Now we combine both the top-level literals as well as the multi-part literals
    val res : OrderClause = predLiterals ++ eqLiterals ++ negLiterals

    // println("conjToClause(" + conj + ", " + negated + ")")
    // println("\t" + res)
    res
  }

  def clauseWidth(conj : Conjunction) = conjToClause(fullInst(conj, "clauseWidth")._1, false).length

    // TODO: Is this sound, ask Philipp!
  def isUnitClause(conj : Conjunction) : Boolean = conj.boundVariables.size == 0


  def extractConstants(conjs : List[Conjunction]) : BREUOrder = {
    (for (c <- conjs) yield c.constants).toSet.flatten.toList.map((_, false))
  }

  def solve(givenFor : Conjunction, termOrder : TermOrder) = {

    // Since the formula is in CNF, everything should be in the negated conjunctions

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ConnectionProver.AC, givenFor.predConj.size == 0 && givenFor.arithConj.isEmpty)
    //-END-ASSERTION-//////////////////////////////////////////////////////////

    println("\n\nSolving Table")
    val quans = givenFor.quans
    val tmpConstants = for (i <- 0 until givenFor.quans.length) yield (new ConstantTerm("CONSTANT_" + i))
    val tmpOrder = givenFor.order.extend(tmpConstants)
    val closedFor = givenFor.instantiate(tmpConstants)(tmpOrder)
    val negQuans = closedFor.negate.quans

    val inputClauses = closedFor.negate.iterator.toList.reverse

    // println("Input Clauses (DEBUG)")
    // for (c <- inputClauses) 
    //   println("\t" + c + " => " + (conjToClause(fullInst(c, "conv")._1, false)))

    val clauses = for (c <- inputClauses) yield { Conjunction.quantify(negQuans, c, c.order) }

    println("Input Clauses: ")
    for (c <- inputClauses) 
      println("\t" + clauseToString((conjToClause(fullInst(c, "conv")._1, false))))

    val unitInst = for (c <- clauses if isUnitClause(c)) yield conjToClause(fullInst(c, "conv")._1, false)
    val unitClauses = unitInst.map(_(0))

    println("Unit Clauses:\n " + unitClauses.mkString("\t", "\n\t", "\n"))

    val baseOrder = extractConstants(clauses) ++ List((new ConstantTerm("MIN"), false))
    println("Base Order: " + baseOrder)

    def tryFirstClause(idx : Int, maxDepth : Int, maxWidth : Int) :
        (Option[ConnectionTable], Boolean, Boolean) = {

      val (firstClause, terms, newOrder) = fullInst(clauses(idx), "base")

      println("\n\nTrying with inital clause: " + firstClause)

      // We have to extract all terms in the problem
      val initOrder = (terms ++ baseOrder)
      // TODO: Not so nice...

      val unitNodes = unitClauses.map(_._1).flatten : List[Node]
      // TODO: initOrder2!?, come on ...
      val initTable  =
        new ConnectionTable(for ((nodes, extraOrder) <- conjToClause(firstClause, false)) yield {
          val initOrder2 = initOrder ++  extraOrder
          new ConnectionBranch(nodes ++ unitNodes, true, initOrder2)
        }, preSettings)

      maxDepthReached = false
      maxWidthReached = false
      val result = solveTable(initTable, clauses, maxDepth, maxWidth, 0)
      if (result.isEmpty) {
        println("Could not close table")
        (None, maxDepthReached, maxWidthReached)
      } else {
        val finalTable = result.get
        (Some(finalTable), false, false)
      }
    }

    var table = None : Option[ConnectionTable]

    var maxDepth = 8
    var maxWidth = 8
    var reachedMaxDepth = true
    var reachedMaxWidth = true

    while (table.isEmpty && (reachedMaxDepth || reachedMaxWidth)) {
      var tryIdx = 0
      reachedMaxDepth = false
      reachedMaxWidth = false
      println("//-----------------------------")
      println("||  TRYING maxDepth: " + maxDepth)
      println("||  TRYING maxWidth: " + maxWidth)
      println("||")
      println("||")
      while (table.isEmpty && tryIdx < clauses.length) {
        val (resTable, rMaxDepth, rMaxWidth) = tryFirstClause(tryIdx, maxDepth, maxWidth)
        table = resTable
        if (rMaxDepth)
          reachedMaxDepth = true
        if (rMaxWidth)
          reachedMaxWidth = true
        tryIdx += 1
      }

      if (reachedMaxDepth || reachedMaxWidth) {
        println("Increasing depths:")
        if (reachedMaxDepth) {
          maxDepth *=2
          println("\tmaxDepth = " + maxDepth)
        }
        if (reachedMaxWidth) {
          maxWidth *=2
          println("\tmaxWidth = " + maxWidth)
        }
      }
    }

    if (!table.isEmpty) {
      println("\n\n\n\tTable closed\n\n\n")
      val finalTable = table.get
      val (unifiable, finalMap) = finalTable.unifyBranches()
      println("CLOSED TABLE:")
      // println("with order: " + finalOrder.mkString(", "))
      for (b <- finalTable.branches)
        println("\t" + b)
      println("Using: " + finalMap)
      (true, Goal(List(closedFor), Set(), Vocabulary(termOrder), preSettings))
    } else {
      println("Could not close table")
      (false, Goal(List(closedFor), Set(), Vocabulary(termOrder), preSettings))
    }
  }
}
