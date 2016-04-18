/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
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

import ap._
import ap.terfor.{Formula, TermOrder, ConstantTerm}
import ap.terfor.conjunctions.{Conjunction, Quantifier, NegatedConjunctions}
import ap.terfor.preds.{Predicate, Atom, PredConj}
import ap.terfor.equations.EquationConj
import ap.terfor.arithconj.{ArithConj, ModelElement, EqModelElement}
import ap.terfor.substitutions.ConstantSubst
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.TerForConvenience
import ap.proof.goal._
import ap.proof.certificates._
import ap.util.{Logic, Debug, Seqs, Timeout}
import ap.parameters.{GoalSettings, Param}
import ap.proof.tree._
import ap.proof.{Vocabulary, ProofGrounder, ProofMinimiser, ConstantFreedom}
import ap.parser.SimpleClausifier

import scala.collection.mutable.{Stack, ArrayBuffer, ListBuffer}

object ConnectionProver {
  private val AC = Debug.AC_CONNECTION_PROVER
}

class ConnectionProver(depthFirst : Boolean, preSettings : GoalSettings) {

  // Convert a conjunction to a list of clauses (with each node being a formula followed by assumptions)
  def convertConjunction(conj : Conjunction) = {
    val singlePredicates = for (p <- conj.predConj.iterator) yield (p, List())
    val predicatesWithFacts = 
      for (pwf <- conj.negatedConjs) yield {
        val assumptions = ListBuffer() : ListBuffer[PredConj]
        val formulas = ListBuffer() : ListBuffer[PredConj]

        for (p <- pwf.predConj.iterator) {
          if ((p.predicates.size == 1) && (p.predicates subsetOf Param.FUNCTIONAL_PREDICATES(preSettings))) {
            assumptions += p
          } else if (p.predicates.size == 1) {
            formulas += !p
          } else {
            throw new Exception("More than one predicate in predConj!")
          }
        }

        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
        Debug.assertInt(ConnectionProver.AC, formulas.length == 1)
        //-END-ASSERTION-//////////////////////////////////////////////////////////        

        (formulas.head, assumptions.toList)
      }

    (singlePredicates ++ predicatesWithFacts).toList
  }

  // Instantiate first level conj with new variables added to order with prefix
  def inst(conj : Conjunction, prefix : String, order : TermOrder) : (Conjunction, List[(ConstantTerm, Boolean)], TermOrder) = {
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
  def fullInst(conj : Conjunction, prefix : String) = {
    // Instantiate top-level
    val allTerms : ListBuffer[(ConstantTerm, Boolean)] = ListBuffer()

    val (newConj, nt, norder) = inst(conj, prefix, conj.order)
    allTerms ++= nt

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, newConj.negatedConjs.size == 1)
    //-END-ASSERTION-//////////////////////////////////////////////////////////

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
    (finalConj, allTerms, negOrder)
  }

  def checkUnifiability(pred1 : PredConj, pred2 : PredConj, equations : List[PredConj], order : List[(ConstantTerm, Boolean)]) : Boolean = { 
    // println("Checking unifiability!")
    // println("Given:")
    // for (e <- equations) println("\t" + e)
    // println("with Order:")
    // println(order)
    // println("Unify: \n\t" + pred1 + " ?= " + pred2)
    if (checkUnifiabilityAux(pred1, pred2, equations, order)) {
      // println("UNIFIABLE")
      true
    } else {
      // println("Diff!")
      false
    }
  }

  // Converts a pc representing a conjunction to a triple
  def convertEquation(pc : PredConj) = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, pc.isLiteral && pc.positiveLits.length == 1)
    //-END-ASSERTION-//////////////////////////////////////////////////////////
    val atom = pc.positiveLits(0)
    val fun = atom.pred
    val args = atom.take(atom.length-1).map(x => x.lastTerm.constants.head)
    val res = atom(atom.length-1).lastTerm.constants.head
    (fun, args, res)
  }

  // Returns true if pred1 and pred2 can be unified, given the equations and order
  def checkUnifiabilityAux(pred1 : PredConj, pred2 : PredConj, equations : List[PredConj], order : List[(ConstantTerm, Boolean)]) : Boolean = {

    val ccuSolver = new ccu.LazySolver[ConstantTerm, Predicate](() => Timeout.check, Param.CLAUSIFIER_TIMEOUT(preSettings))
    
    // We need to keep track of domains
    val domain = scala.collection.mutable.Map() : scala.collection.mutable.Map[ConstantTerm,Set[ConstantTerm]]
    for ((t, uni) <- order.reverse) {
      domain += (t -> Set(t))
      if (uni) {
        for (k <- domain.keys) {
          domain += (t -> (domain(t) + k))
        }
      }
    }

    // println("order: " + order)
    // println("domain: "+  domain)

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, pred1.isLiteral && pred2.isLiteral)
    //-END-ASSERTION-//////////////////////////////////////////////////////////

    // Two cases, either pred1 and !pred2 or !pred1 and pred2
    if (!((pred1.negativeLits.length == 1 && pred2.positiveLits.length == 1) ||
      (pred2.negativeLits.length == 1 && pred1.positiveLits.length == 1))) {
      return false
    }

    println("\tNegation-compatible")

    // They have to share predicate symbol
    val pred1atom = (pred1.negativeLits ++ pred1.positiveLits).head
    val pred2atom = (pred2.negativeLits ++ pred2.positiveLits).head

    if (pred1atom.pred != pred2atom.pred)
      return false

    println("\tPredicate-compatible")

    // Unify each argument
    val argGoals = 
      for ((arg1, arg2) <- pred1atom zip pred2atom) yield {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
        Debug.assertPre(ConnectionProver.AC, arg1.termIterator.size == 1 && arg2.termIterator.size == 1)
        //-END-ASSERTION-//////////////////////////////////////////////////////////
        println("\t" + arg1 + "\t?=\t" + arg2)
        (arg1.lastTerm.constants.head, arg2.lastTerm.constants.head)
      }

    // Convert functions
    val eqs = 
      for (e <- equations) yield {
        convertEquation(e)
      }
    val problem = ccuSolver.createProblem(domain.toMap, List(List(argGoals)), List(eqs))
    val result =  problem.solve
    println(result)
    if (result == ccu.Result.SAT) {
      // println(problem.getModel)
      true
    } else {
      false
    }
  }



  def pickBranch(branchList : List[(List[PredConj], Boolean)]) : Option[(List[PredConj], Boolean)] = {
    if (branchList.isEmpty)
      None
    val (b, closed) = branchList.head
    if (!closed)
      Some(branchList.head)
    else
      pickBranch(branchList.tail)
  }

  def pickClause(targetClause : PredConj, clauseList : List[Conjunction], prefix : String, terms : List[(ConstantTerm, Boolean)]) :
      Option[(List[Int], List[(PredConj, List[PredConj])], List[(ConstantTerm, Boolean)])] = {
    if (clauseList.isEmpty) {
      None
    } else {
      // Try using the first of clauseList
      val (clause, newTerms, newOrder) = fullInst(clauseList.head, prefix)

      val tmpTerms = newTerms ++ terms

      // Transform into clauses
      val clauses =
        if (clause.negatedConjs.isEmpty) {
          println("\tNot a disjunction!")
          println("\t" + clause)
          throw new Exception("Not implemented")
        } else {
          //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
          Debug.assertPre(ConnectionProver.AC, clause.predConj.size == 0 && clause.arithConj.isEmpty)
          Debug.assertPre(ConnectionProver.AC, clause.negatedConjs.size == 1)
          //-END-ASSERTION-//////////////////////////////////////////////////////////
          convertConjunction(clause.negatedConjs(0))
        }

      // Look if any c in clauses can be unified with targetClause
      val options = for (c <- 0 until clauses.length; if checkUnifiability(targetClause, clauses(c)._1, clauses(c)._2, tmpTerms.toList)) yield c
      if (options.length > 0)
        Some((options.toList, clauses, tmpTerms.toList))
      else
        pickClause(targetClause, clauseList.tail, prefix, terms)
    }
  }

  def extractEquations(list : List[PredConj]) : List[PredConj] = {
    if (list.isEmpty)
      List()
    else if ((list.head.predicates.size == 1) &&
      (list.head.predicates subsetOf Param.FUNCTIONAL_PREDICATES(preSettings)))
      list.head :: extractEquations(list.tail)
    else
      extractEquations(list.tail)
  }

  def extractFormulas(list : List[PredConj]) : List[PredConj] = {
    if (list.isEmpty)
      List()
    else if ((list.head.predicates.size == 1) &&
      (list.head.predicates subsetOf Param.FUNCTIONAL_PREDICATES(preSettings)))
      extractFormulas(list.tail)
    else
      list.head :: extractFormulas(list.tail)
  }

  def pickNode(targetClause : PredConj, formList : List[PredConj], eqList : List[PredConj], terms : List[(ConstantTerm, Boolean)]) :
      Option[(List[Int], List[(PredConj, List[PredConj])], List[(ConstantTerm, Boolean)])] = {
    if (formList.isEmpty) {
      None
    } else {
      val node = formList.head
      if (checkUnifiability(targetClause, node, eqList, terms.toList))
        Some((List(0), List((node, List())), List()))
      else
        pickNode(targetClause, formList.tail, eqList, terms)
    }
  }

  // main solving loop
  def loop(branches : List[(List[PredConj], Boolean)], 
           terms : List[(ConstantTerm, Boolean)], 
           CNF : List[Conjunction],
           iteration : Int) :
      (List[(List[PredConj], Boolean)], List[(ConstantTerm, Boolean)]) = {

    println("Iteration: " + iteration)
    println("Open branches:")
    for (b <- branches; if !b._2)
      println("\t" + b._1)
    println("Current terms:")
    println("\t" + terms)

    // Pick a branch
    val tmpBranch = pickBranch(branches)
    if (tmpBranch.isEmpty) {
      throw new Exception("Handle all branhces closed!")
      return (List(), List())
    }

    val otherBranches = branches.filter(x => x != tmpBranch.get)
    val branch = tmpBranch.get._1
    val endOfBranch = branch(0)

    println("Extending branch: \n\t" + branch)

    // Start by trying to close using a clause from the tree
    val eqs = extractEquations(branch.tail)
    val forms = extractFormulas(branch.tail)
    val branchNode = pickNode(endOfBranch, forms, eqs, terms)

    val sel = 
      if (!branchNode.isEmpty) {
        println("Using node from tree: " + branchNode)
        branchNode
      } else {
        // Otherwise, use clause from given clauses
        val clauseNode = pickClause(endOfBranch, CNF, "branch_" + iteration, terms)
        if (clauseNode.isEmpty) {
          throw new Exception("Handle all branch cannot be extended!")
          return (List(), List())
        } else {
          clauseNode
        }
      }

    // Do we need to keep the newOrder (from fullInst)?
    val (selOptions, selClause, selTerms) = sel.get
    println("Selected Clause: " + selClause)

    // Now we have to create new branches
    // Take the current branch and copy once for each literal in the selected clause
    val newBranches = for (i <- 0 until selClause.length) yield {
      // This might not work!
      val closed = selOptions contains i
      val flattened = selClause(i)._1 :: selClause(i)._2
      (flattened ++ branch, closed)
    }

    (otherBranches.toList ++ newBranches.toList, selTerms)
  }



  def solve(closedFor : Conjunction, termOrder : TermOrder) = {
    // Since the formula is in CNF, everything should be in the negated conjunctions
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ConnectionProver.AC, closedFor.predConj.size == 0 && closedFor.arithConj.isEmpty)
    //-END-ASSERTION-//////////////////////////////////////////////////////////

    // 
    val clauses = 
      (for (nc <- closedFor.negatedConjs) yield
        nc.negatedConjs).flatten.map(x => !x).reverse.toList

    // Pick first clause
    val firstIdx = 0
    val (firstClause, terms, newOrder) = fullInst(clauses(firstIdx), "base")

    println("FirstClause: " + clauses(firstIdx))
    println("Inst: " + firstClause)


    var branches  = 
      for ((form, ass) <- convertConjunction(firstClause)) yield {
        println("(FORM, ASS): " + ((form, ass)))
        ((form :: ass), false)
      }

    println("Branch: " + branches)

    // Ensure we have a minimal term
    var order = (terms ++ List((new ConstantTerm("MIN"), false))).toList
    var iteration = 0

    while (branches.exists(x => !x._2)) {
      val (newBranches, newOrder) = loop(branches, order, clauses, iteration)
      iteration += 1
      branches = newBranches
      order = newOrder
    }

    println("Tree closed: ")
    for (b <- branches) {
      println("\t" + b._1)
    }
    Goal(List(closedFor), Set(), Vocabulary(termOrder), preSettings)
  }
}
