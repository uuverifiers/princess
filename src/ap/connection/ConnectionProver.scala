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

  // Debug 
  val DEBUG = true
  var stepCount = 0
  def dprintln(str : String) = if (DEBUGPrint) println(str)
  val funPreds = Param.FUNCTIONAL_PREDICATES(preSettings)

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


  /**
    * Instantiates conj, where new terms are named using prefix. 
    * 
    *  Returns: 
    *    -Instantiated Conjunction,
    *    -New constant terms (and a Boolean indicating if they are Universally Quantified)
    *    -Updated TermOrder (which might be thrown away...)
    */
  def instantiateAux(conj : Conjunction, prefix : String, to : TermOrder) :
      (Conjunction, BREUOrder, TermOrder) = {
    
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

    // Pull out all universals to the front...

    val newBREUOrder = allTerms.toList.reverse.filter(!_._2) ++ allTerms.toList.reverse.filter(_._2)

    (finalConj, newBREUOrder, termOrder)
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
    dprintln("Trying step " + step + "\t(" + stepCount + ")")
    stepCount += 1
    val closedTable =
      if (step == 0) {
        Some(table.close(branchIdx, false))
      } else ap.util.Timer.measure("Extending Table") {
        val (clause, idx) = findLiteral(inputClauses, step - 1)
        dprintln("\tExtending with: " + clause)
        val (instClause, newBREUOrder) = fullInst(clause, "branch_" + iteration)
        val (pseudoClause, tmpBREUOrder) = PseudoClause.CTC(instClause, funPreds)
        val firstLiteral = pseudoClause(idx)
        val finalBREUOrder = tmpBREUOrder ++ newBREUOrder
        dprintln("\tpicked literal: " + firstLiteral + " $ " + finalBREUOrder)

        // TODO: tmpBREUOrder should only be existentials...
        val extendedTable = table.extendBranch(branchIdx, pseudoClause, idx, finalBREUOrder)
        extendedTable.closeSafe(branchIdx, strong)
      }

    if (!closedTable.isEmpty && closedTable.get.closable(disequalities))
      closedTable
    else
      None
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
      // val branchIdx = table.firstOpen
      val branchIdx = table.shortestOpen

      println("\n//--------- " + iteration + " -------------")
      println("|| extending (" + branchIdx + ")")
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
          // res.get.diseqPairs.toList ++ 
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


  def clauseWidth(conj : Conjunction) = PseudoClause.CTC(fullInst(conj, "clauseWidth")._1, funPreds)._1.length

  // TODO: Is this sound, ask Philipp!
  def isUnitClause(conj : Conjunction) : Boolean = conj.boundVariables.size == 0

  def extractConstants(conjs : List[Conjunction]) : BREUOrder = {
    (for (c <- conjs) yield c.constants).toSet.flatten.toList.map((_, false))
  }

  /*
   * Given a formula and a term ordering, and tries to prove it using connection tableuax
   */
  def solve(givenFor : Conjunction, termOrder : TermOrder) : (Boolean, ap.proof.goal.Goal) = ap.util.Timer.measure("Solve") {

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

    dprintln("Input Clauses (non-intantiated): ")
    for (c <- clauses)
      println(c)


    val strs = 
      for (c <- clauses) yield {
        val (pseudoClause, breuOrder) = PseudoClause.CTC(fullInst(c, "")._1, funPreds, DEBUGPrint)
        "" + c + "\n\t->" + pseudoClause
      }

    // println("Input Clauses (fromConjunction):")
    // for (c <- clauses) {
    //   val (pseudoClause, breuOrder) = PseudoClause.fromConjunction(fullInst(c, "")._1, funPreds, DEBUGPrint)
    //   println("\t" + pseudoClause)
    // }

    dprintln("Input Clauses (CTC):")    
    println(strs.mkString("\n"))



    // Put all unit clauses on the main branch

    var initBREUOrder = List() : BREUOrder
    val unitClauses : List[PseudoClause] =
      for (c <- clauses if isUnitClause(c)) yield {
        val (clause, tmpBREUOrder) = PseudoClause.CTC((fullInst(c, "conv")._1), funPreds)
        initBREUOrder ++= tmpBREUOrder
        clause
      }

    if (!unitClauses.isEmpty)
      println(unitClauses.map(_.toString).mkString("Unit Clauses:\n\t", "\n\t","\n"))    

    def tryFirstClause(idx : Int, maxIterations : Int) :
        (Option[ConnectionTable], Boolean) = {

      val (firstClause, newTerms) = fullInst(clauses(idx), "base")
      val baseOrder = initBREUOrder ++ extractConstants(clauses) ++ List((new ConstantTerm("MIN"), false))
      val (initClause, someBREUOrder) = PseudoClause.CTC(firstClause, funPreds)

      // TODO: This is not very elegant, but hopefully correct?
      val initOrder = (newTerms ++ someBREUOrder ++ baseOrder)

      println("\n//-----------------------------")      
      println("||Trying with initial clause: " + initClause)
      println("|| initOrder: " + initOrder)
      println("|| newTerms: " + newTerms)
      println("\\-----------------------------")      

      val initTable  =
        new ConnectionTable(for (plit <- initClause.pseudoLiterals) yield {
          new ConnectionBranch(plit.nodes ++ unitClauses.map(_.head.nodes).flatten, ClosedStyle.Open, initOrder)
        }, preSettings, DEBUGPrint)

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

      while (table.isEmpty && tryIdx < clauses.length) {
        val (t, mr) = tryFirstClause(tryIdx, maxIteration)
        table = t
        maxReached |= mr
        tryIdx += 1
      }

      if (maxReached) {
        println("Increasing max iteration:")
        maxIteration += 1
      }
    }

    println(ap.util.Timer)
    if (!table.isEmpty) {
      println("\n\n\n\tTable closed\n\n\n")
      val finalTable = table.get
      val finalMap = finalTable.unifyBranches()
      println("CLOSED TABLE:")
      println(finalTable)
      println("Using: " + finalMap.get)
      (true, Goal(List(givenFor), Set(), Vocabulary(termOrder), preSettings))
    } else {
      println("Could not close table")
      (false, Goal(List(givenFor), Set(), Vocabulary(termOrder), preSettings))
    }
  }
}


