//
// Todo:
// PUZ001+1.p, Missing quantifiers??
//
// TODO: Fix terms vs order (BREUterms?)



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

  // A branch is its list of formulas, an optional pair of nodes
  // closing the branch and a number describing what steps have been
  // tried .The steps are in range 
  // [0 .. branch.length - 1 .. branch.length - 1 + |Input Clauses*Clause length|]. 
  // I.e., first we try the nodes on the branch, then the input clauses.
  type Branch = (List[PredConj], Option[(Int, Int)], Int)
  type Table = List[Branch]
  type Literal = (PredConj, List[PredConj])

  // A term in a BREUOrder which is (_, false) is a constant while
  // (_, true) is a variable which can take the value of any variable or
  // constant earlier in the order.
  type BREUOrder = List[(ConstantTerm, Boolean)]

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

    println("fullInst(" + conj + ") => " + retVal)
    retVal
  }

  def checkUnifiability(pred1 : PredConj, pred2 : PredConj, equations : List[PredConj], order : BREUOrder) : Boolean = { 
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

  def unifyBranches(branches : List[Branch], order : BREUOrder) : (Boolean, Option[Map[ConstantTerm, ConstantTerm]]) = {
    val problems = for (b <- branches) yield branchToBreu(b, order)

    val ccuSolver = new ccu.LazySolver[ConstantTerm, Predicate](() => Timeout.check, Param.CLAUSIFIER_TIMEOUT(preSettings))
    val domains = problems.head.get._1
    val argGoals = problems.map(_.get._2.head)
    val eqs = problems.map(_.get._3.head)
    val problem = ccuSolver.createProblem(domains, argGoals, eqs)
    val result =  problem.solve
    if (result == ccu.Result.SAT)
      (true, Some(problem.getModel))
    else
      (false, None)
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
    (fun, args.toList, res)
  }

  // Returns true if pred1 and pred2 can be unified, given the equations and order
  def checkUnifiabilityAux(pred1 : PredConj, pred2 : PredConj, equations : List[PredConj], order : BREUOrder) : Boolean = {

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

    // println("\tNegation-compatible")

    // They have to share predicate symbol
    val pred1atom = (pred1.negativeLits ++ pred1.positiveLits).head
    val pred2atom = (pred2.negativeLits ++ pred2.positiveLits).head

    if (pred1atom.pred != pred2atom.pred)
      return false

    // println("\tPredicate-compatible")

    // Unify each argument
    val argGoals = 
      for ((arg1, arg2) <- pred1atom zip pred2atom) yield {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
        Debug.assertPre(ConnectionProver.AC, arg1.termIterator.size == 1 && arg2.termIterator.size == 1)
        //-END-ASSERTION-//////////////////////////////////////////////////////////
        // println("\t" + arg1 + "\t?=\t" + arg2)
        (arg1.lastTerm.constants.head, arg2.lastTerm.constants.head)
      }

    // Convert functions
    val eqs = 
      for (e <- equations) yield {
        convertEquation(e)
      }
    val problem = ccuSolver.createProblem(domain.toMap, List(List(argGoals)), List(eqs))
    val result =  problem.solve
    // println(result)
    if (result == ccu.Result.SAT) {
      // println(problem.getModel)
      true
    } else {
      false
    }
  }

  // Returns true if pred1 and pred2 can be unified, given the equations and order
  def structuralUnifiable(pred1 : PredConj, pred2 : PredConj) : Boolean = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, pred1.isLiteral && pred2.isLiteral)
    //-END-ASSERTION-//////////////////////////////////////////////////////////

    // Two cases, either pred1 and !pred2 or !pred1 and pred2
    if (!((pred1.negativeLits.length == 1 && pred2.positiveLits.length == 1) ||
      (pred2.negativeLits.length == 1 && pred1.positiveLits.length == 1))) {
      return false
    }

    // println("\tNegation-compatible")
    // They have to share predicate symbol
    val pred1atom = (pred1.negativeLits ++ pred1.positiveLits).head
    val pred2atom = (pred2.negativeLits ++ pred2.positiveLits).head

    if (pred1atom.pred != pred2atom.pred)
      return false

    true
  }

  def structuralClosable(branch : Branch) : Boolean = {
    val (b, cp, step) = branch
    if (cp.isEmpty) {
      false
    } else {
      val (cp1, cp2) = cp.get
      val pred1 = b(cp1)
      val pred2 = b(cp2)
      structuralUnifiable(pred1, pred2)
    }
  }

  def branchToBreu(branch : Branch, order : BREUOrder) : 
      Option[(Map[ConstantTerm,Set[ConstantTerm]], List[List[List[(ConstantTerm, ConstantTerm)]]], List[List[(Predicate, List[ConstantTerm], ConstantTerm)]])] = {
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

    val (nodes, closed, _) = branch
    // TODO: How do we order 
    val pred1 = nodes(closed.get._1)
    val pred2 = nodes(closed.get._2)

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, pred1.isLiteral && pred2.isLiteral)
    //-END-ASSERTION-//////////////////////////////////////////////////////////

    // Two cases, either pred1 and !pred2 or !pred1 and pred2
    if (!((pred1.negativeLits.length == 1 && pred2.positiveLits.length == 1) ||
      (pred2.negativeLits.length == 1 && pred1.positiveLits.length == 1))) {
      return None
    }

    // println("\tNegation-compatible")

    // They have to share predicate symbol
    val pred1atom = (pred1.negativeLits ++ pred1.positiveLits).head
    val pred2atom = (pred2.negativeLits ++ pred2.positiveLits).head

    if (pred1atom.pred != pred2atom.pred) {
      return None
    }

    // println("\tPredicate-compatible")

    // Unify each argument
    println("pred1atom (" + pred1atom.getClass + ") : " + pred1atom )
    println("pred2atom (" + pred2atom.getClass + ") : " + pred2atom)

    val argGoals = 
      for ((arg1, arg2) <- pred1atom zip pred2atom) yield {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
        Debug.assertPre(ConnectionProver.AC, arg1.termIterator.size == 1 && arg2.termIterator.size == 1)
        //-END-ASSERTION-//////////////////////////////////////////////////////////
        println("\t" + arg1 + "\t?=\t" + arg2)
        println("\t" + arg1.getClass + " \t?=\t" + arg2.getClass)
        (arg1.lastTerm.constants.head, arg2.lastTerm.constants.head)
      }

    val equations = extractEquations(nodes)

    // Convert functions
    val eqs = 
      for (e <- equations) yield {
        convertEquation(e)
      }
    Some((domain.toMap, List(List(argGoals.toList)).toList, List(eqs)))
    // val problem = ccuSolver.createProblem(domain.toMap, List(List(argGoals)), List(eqs))
    // val result =  problem.solve
    // println(result)
    // if (result == ccu.Result.SAT) {
    //   // println(problem.getModel)
    //   true
    // } else {
    //   false
    // }
    // true
  }





  def pickBranch(branchList : List[Branch]) : Option[Branch] = {
    if (branchList.isEmpty)
      None
    val (b, closed, _) = branchList.head
    if (closed.isEmpty)
      Some(branchList.head)
    else
      pickBranch(branchList.tail)
  }

  def pickClauseAux(targetClause : PredConj, clauseList : List[Conjunction], prefix : String, terms : BREUOrder) :
      Option[(List[Int], List[(PredConj, List[PredConj])], BREUOrder)] = {
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
        pickClauseAux(targetClause, clauseList.tail, prefix, terms)
    }
  }

  def pickClause(targetClause : PredConj, clauseList : List[Conjunction], prefix : String, terms : BREUOrder) =
    pickClauseAux(targetClause, clauseList, prefix, terms)

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

  def pickNodeAux(targetClause : PredConj, formList : List[PredConj], eqList : List[PredConj], terms : BREUOrder, idx : Int) :
      Option[(List[Int], List[(PredConj, List[PredConj])], BREUOrder)] = {
    if (formList.isEmpty) {
      None
    } else {
      val node = formList.head
      if (checkUnifiability(targetClause, node, eqList, terms.toList))
        Some((List(idx), List((node, List())), terms))
      else
        pickNodeAux(targetClause, formList.tail, eqList, terms, idx - 1)
    } 
  } 

  def pickNode(targetClause : PredConj, formList : List[PredConj], eqList : List[PredConj], terms : BREUOrder) = 
    pickNodeAux(targetClause, formList, eqList, terms, formList.length - 1)

  // main solving loop
  def loop(branches : List[Branch], 
           terms : BREUOrder, 
           CNF : List[Conjunction],
           iteration : Int) :
      (List[Branch], BREUOrder) = {

    println("Iteration: " + iteration)
    println("Open branches:")
    for (b <- branches; if b._2.isEmpty)
      println("\t" + b._1)
    println("Current terms:")
    println("\t" + terms)

    // Pick a branch
    val tmpBranch = pickBranch(branches)
    if (tmpBranch.isEmpty) {
      throw new Exception("Handle all branches closed!")
      return (List(), List())
    }

    val otherBranches = branches.filter(x => x != tmpBranch.get)
    val branch = tmpBranch.get._1
    val idxOfBranch = tmpBranch.get._1.length - 1
    val endOfBranch = branch(0)

    println("Extending branch: \n\t" + branch)

    // Start by trying to close using a clause from the tree
    val eqs = extractEquations(branch.tail)
    val forms = extractFormulas(branch.tail)
    val branchNode = pickNode(endOfBranch, forms, eqs, terms)

    val tmpSel = 
      if (!branchNode.isEmpty) {
        println("Using node from tree: " + branchNode)
        (true, branchNode)
      } else {
        // Otherwise, use clause from given clauses
        val clauseNode = pickClause(endOfBranch, CNF, "branch_" + iteration, terms)
        if (clauseNode.isEmpty) {
          throw new Exception("Handle all branch cannot be extended!")
          return (List(), List())
        } else {
          (false, clauseNode)
        }
      }

    // Do we need to keep the newOrder (from fullInst)?
    val (fromBranch, sel) = tmpSel
    val (selOptions, selClause, selTerms) = sel.get
    println("Selected Clause: " + selClause)
    println("\tfrom: " + selOptions)

    // If closed from branch, we need not create any new branches
    if (fromBranch) {
      val nodeIdx = branch.length  - (branch indexOf selClause.head._1) - 1
      println("Using node from branch: " + selClause + "(" + nodeIdx +")")
      (otherBranches.toList ++ List((branch, Some(idxOfBranch, nodeIdx), nodeIdx)), selTerms)
    } else {
      // Now we have to create new branches
      // Take the current branch and copy once for each literal in the selected clause
      val newBranches = for (i <- 0 until selClause.length) yield {
        // This might not work!
        // TODO: Currently we only consider the first option
        val closed =
          if (selOptions.head == i)
            Some(idxOfBranch, idxOfBranch+1)
          else
            None
        val flattened = selClause(i)._1 :: selClause(i)._2
        (flattened ++ branch, closed, 0)
      }
      (newBranches.toList ++ otherBranches.toList, selTerms)
    }
  }



  // def checkClause(targetAtom : PredConj, clause : Conjunction, prefix : String, terms : BREUOrder) :
  //     Option[(List[Int], List[(PredConj, List[PredConj])], BREUOrder)] = {
  //   // Try using the first of clauseList
  //   val (clause, newTerms, newOrder) = fullInst(clause, prefix)
  //   val tmpTerms = newTerms ++ terms

  //   //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
  //   Debug.assertPre(ConnectionProver.AC, clause.negatedConjs.isEmpty)
  //   Debug.assertPre(ConnectionProver.AC, clause.predConj.size == 0 && clause.arithConj.isEmpty)
  //   Debug.assertPre(ConnectionProver.AC, clause.negatedConjs.size == 1)
  //   //-END-ASSERTION-//////////////////////////////////////////////////////////

  //   // Transform into clauses
  //   val clauses = convertConjunction(clause.negatedConjs(0))

  //   // Look if any c in clauses can be unified with targetClause
  //   val options = for (c <- 0 until clauses.length; if checkUnifiability(targetClause, clauses(c)._1, clauses(c)._2, tmpTerms.toList)) yield c
  //   if (options.length > 0) 
  //     Some((options.toList, clauses, tmpTerms.toList))
  //   else
  //     pickClauseAux(targetClause, clauseList.tail, prefix, terms)
  // }

  def findStatement(inputClauses : List[Conjunction], step : Int) :
      (Conjunction, Int) = {
    if (step >= clauseWidth(inputClauses.head))
      findStatement(inputClauses.tail, step - clauseWidth(inputClauses.head))
    else
      (inputClauses.head, step)
  }


  // PRE: there must be at least one open branch
  // TODO: Make sure branches never begin with a function! Or should we?
  def incLoop(branches : List[Branch], 
           terms : BREUOrder, 
           inputClauses : List[Conjunction],
           maxDepth : Int,
           iteration : Int) :
      Option[(List[Branch], BREUOrder)] = {

    println("//-------------------------")
    println("|| Starting incremental iteration " + iteration)
    println("|| Branches: ")
    for (b <- branches) {
      if (b._2.isEmpty)
        println("||\t(" + b._3 + ") " + b._1)
      else
        println("||\t(" + b._3 + ") " + b._1 + " closed using " + b._2.get)
    }
    println("|| Current terms:")
    println("||\t" + terms)

    // Pick a branch -- Always pick first open branch
    // TODO: Any way of making branch a val and branchStep a var?
    val extendingBranch = branches.find(_._2.isEmpty).get
    var (branch, _, branchStep) = extendingBranch
    val branchIdx = branches.indexOf(extendingBranch)
    val branchAtom = branch(0)
    val branchEqs = extractEquations(branch)

    println("|| Extending branch (" + branchIdx + "): ")
    println("||\t" + branch)

    // If branch is too long, stop
    if (branch.length >= maxDepth)
      return None

    var candidateAtom = None : Option[PredConj]
    var candidateBranches = List() : List[Branch]
    var candidateOrder = terms : BREUOrder

    // We use the branchStep to decide where to search for the new candidate
    // TODO: Once again, negatedConjs(0), also, -1?
    // val maxStep = branch.length + (inputClauses.map((x : Conjunction) => clauseWidth(x.negatedConjs(0))).sum) - 1
    val maxStep = branch.length + (inputClauses.map(clauseWidth(_)).sum)

    while (branchStep < maxStep && candidateAtom.isEmpty) {
      println("branchStep: " + branchStep)
      val (tmpEqs, tmpAtom, tmpOrder, tmpBranches) = 
      if (branchStep < branch.length) {
        // Try unifying with node on branch
        (List(), branch(branchStep), List(), List())
      } else {
        // Try unifying with input clause, first we try first clause, first statement,
        // then first clause, second statement, ...
        val (clause, idx) = findStatement(inputClauses, branchStep - branch.length)
        val (instClause, newOrder, _) = fullInst(clause, "branch_" + iteration)
        // TODO: This should not be here, negatedConjs should probably be used somewhere else...
        val stmts = newConvertConjunction(instClause.negatedConjs(0))
        val (forms, eqs) = stmts(idx)
        val newBranches = (for (i <- 0 until stmts.length; if i != idx) yield (stmts(i)._1 ++ stmts(i)._2 ++ branch).toList).toList
        (eqs, forms.head, newOrder, newBranches)
      }

      val checkEqs = tmpEqs ++ branchEqs
      val checkOrder = (tmpOrder ++ terms).toList
      val checkBranch = (tmpAtom :: branch, Some((0, 1)), branchStep)
      val checkBranches = 
        checkBranch :: ((for (i <- 0 until branches.length; if (i != branchIdx); if (!branches(i)._2.isEmpty)) yield branches(i))).toList
      // if (checkUnifiability(branchAtom, tmpAtom, checkEqs, checkOrder)) {
      lazy val (unifiable, model) = unifyBranches(checkBranches, checkOrder)
      if (structuralUnifiable(tmpAtom, branchAtom) && unifiable) {
        candidateAtom = Some(tmpAtom)
        candidateBranches = tmpBranches.map((_, None : Option[(Int, Int)], 0))
        candidateOrder = checkOrder
      } else { 
        branchStep += 1
      }
    }

    if (candidateAtom.isEmpty) {
      println("Branch cannot be closed!")
      None
    } else {
      // val closingPair = Some((0, branchStep))
      val closingPair = Some((0, 1))
      println("|| Branch closed by: " + candidateAtom.get)
      println("||\twith new branches")
      for (b <- candidateBranches)
        println("||\t" + b)
      // TODO: Should we add one upon closing or when initating?
      val closedBranch = (candidateAtom.get :: branch, closingPair, branchStep+1)
      val newTable = 
        (for (i <- 0 until branchIdx) yield branches(i)) ++ 
        (closedBranch :: candidateBranches) ++
        (for (i <- (branchIdx + 1) until branches.length) yield branches(i))
      Some((newTable.toList, candidateOrder))
    }
  }


  def solveTable(
    table : Table,
    terms : BREUOrder,
    inputClauses : List[Conjunction],
    maxDepth : Int,
    maxWidth : Int,
    iteration : Int) :
      Option[(List[Branch], BREUOrder)] = {

    println("//-------------------------")
    println("|| Starting recursive iteration " + iteration)
    println("|| Branches: ")
    for (b <- table) {
      if (b._2.isEmpty)
        println("||\t(" + b._3 + ") " + b._1)
      else
        println("||\t(" + b._3 + ") " + b._1 + " closed using " + b._2.get)
    }
    // println("|| Current terms:")
    // println("||\t" + terms)

    // Pick a branch -- Always pick first open branch
    // TODO: Any way of making branch a val and branchStep a var?
    val extendingBranch = table.find(_._2.isEmpty)
    if (extendingBranch.isEmpty)
      return Some((table, terms))

    var (branch, _, _) = extendingBranch.get
    val branchIdx = table.indexOf(extendingBranch.get)
    val branchAtom = branch(0)
    val branchEqs = extractEquations(branch)

    println("|| Extending branch (" + branchIdx + "): ")
    println("||\t" + branch)

    // If branch is too long, stop
    if (branch.length >= maxDepth) {
      println("|| MAX DEPTH REACHED")
      return None
    }

    if (table.length >= maxWidth) {
      println("|| MAX WIDTH REACHED")
      return None
    }

    def tryStep(step : Int) = {
      val (closeB, otherB, tmpOrder) : (Branch, List[Branch], BREUOrder) =
        if (step < branch.length) {
          // Try unifying with node on branch
          val closingBranch = (branch, Some(0, step), step)
          (closingBranch, List(), List())
        } else {
          // Try unifying with input clause, first we try first clause, first statement,
          // then first clause, second statement, ...
          val (clause, idx) = findStatement(inputClauses, step - branch.length)
          val (instClause, newOrder, _) = fullInst(clause, "branch_" + iteration)
          // TODO: This should not be here, negatedConjs should probably be used somewhere else...
          // val stmts = newConvertConjunction(instClause.negatedConjs(0))
          val stmts = conjToClause(instClause, false)
          val allBranches = (for (i <- 0 until stmts.length) yield (stmts(i)._1 :: stmts(i)._2 ++ branch).toList).toList
          val closingPair = Some((0, 1 + stmts(idx)._2.length))
          val closingBranch = (allBranches(idx), closingPair, step)
          val otherBranches =  
            (allBranches.take(idx) ++ allBranches.drop(idx + 1)).map((_, None : Option[(Int, Int)], 0))
          (closingBranch, otherBranches, newOrder)
        }

      val checkOrder = (tmpOrder ++ terms).toList
      val checkBranches =
        closeB :: (for (i <- 0 until table.length; if (i != branchIdx); if (!table(i)._2.isEmpty)) yield table(i)).toList
      lazy val (unifiable, model) = unifyBranches(checkBranches, checkOrder)
      if (structuralClosable(closeB) && unifiable) {
        val newTable =
          (for (i <- 0 until branchIdx) yield table(i)) ++
        (closeB :: otherB) ++
        (for (i <- (branchIdx + 1) until table.length) yield table(i))
        Some((newTable.toList, checkOrder))
      } else {
        None
      }
    }

    def candidateStep(step : Int) = {
      val closeB =
        if (step < branch.length) {
          // Try unifying with node on branch
          val closingBranch = (branch, Some(0, step), step)
          (closingBranch)
        } else {
          // Try unifying with input clause, first we try first clause, first statement,
          // then first clause, second statement, ...
          val (clause, idx) = findStatement(inputClauses, step - branch.length)
          val (instClause, newOrder, _) = fullInst(clause, "branch_" + iteration)
          // TODO: This should not be here, negatedConjs should probably be used somewhere else...
          // val stmts = newConvertConjunction(instClause.negatedConjs(0))
          val stmts = conjToClause(instClause, false)
          val allBranches = (for (i <- 0 until stmts.length) yield (stmts(i)._1 :: stmts(i)._2 ++ branch).toList).toList
          // Close this node with node above (ignoring the added equations)
          // TODO: Here we have a bug
          val closingPair = Some((0, 1 + stmts(idx)._2.length))
          val closingBranch = (allBranches(idx), closingPair, step)
          closingBranch
        }

      structuralClosable(closeB)
    }

    // We use the branchStep to decide where to search for the new candidate
    // TODO: Once again, negatedConjs(0), also, -1?
    // val maxStep = branch.length + (inputClauses.map((x : Conjunction) => clauseWidth(x.negatedConjs(0))).sum) - 1
    val maxStep = branch.length + (inputClauses.map(clauseWidth(_)).sum)
    println("|| MaxStep: " + maxStep)
    // println("|| \t" + inputClauses)
    // println("|| \t" + inputClauses.map(newConvertConjunction(_)))
    // println("|| \t" + inputClauses.map(clauseWidth(_)))
    for (c <- inputClauses) {
      println("|| \t" + c + " => " + conjToClause(c, false) + " (" + clauseWidth(c) + ")")
    }
    var branchStep = 0


    val candidateSteps =
      for (i <- 0 until maxStep; if candidateStep(i)) yield i
    println("|| Candidate Steps: " + candidateSteps)

    // TODO: Should this be <=
    // TODO: We can check only candidate steps instead (or just stop the candidate steps)
    while (branchStep < maxStep) {
      // Try this step
      val res = tryStep(branchStep)
      if (!res.isEmpty) {
        // If actualy closed branch, recurse!
        val (newTable, newOrder) = res.get
        val rec = solveTable(newTable, newOrder, inputClauses, maxDepth, maxWidth, iteration + 1)
        if (!rec.isEmpty)
          return rec
      }
      branchStep += 1
    }
    None
  }



  def predToLiteral(predConj : PredConj, negated : Boolean) : List[Literal] = {
    val assumptions = ListBuffer() : ListBuffer[PredConj]
    val formulas = ListBuffer() : ListBuffer[PredConj]

    for (p <- predConj.iterator) {
      if ((p.predicates.size == 1) && (p.predicates subsetOf Param.FUNCTIONAL_PREDICATES(preSettings))) {
        assumptions += p
      } else if (p.predicates.size == 1) {
        if (negated)
          formulas += !p
        else
          formulas += p
      } else {
        throw new Exception("More than one predicate in predConj!")
      }
    }

    for (f <- formulas.toList) yield (f, assumptions.toList)
  }

  // TODO: What to we do with statements without formulas (only assumptions)
  def cC(conj : Conjunction, negated : Boolean) = {
    val assumptions = ListBuffer() : ListBuffer[PredConj]
    val formulas = ListBuffer() : ListBuffer[PredConj]

    for (p <- conj.predConj.iterator) {
      if ((p.predicates.size == 1) && (p.predicates subsetOf Param.FUNCTIONAL_PREDICATES(preSettings))) {
        assumptions += p
      } else if (p.predicates.size == 1) {
        if (negated)
          formulas += !p
        else
          formulas += p
      } else {
        throw new Exception("More than one predicate in predConj!")
      }
    }

    (formulas, assumptions.toList)
  }

  // Convert a conjunction to a list of clauses (with each node being a formula followed by assumptions)
  def newConvertConjunction(conj : Conjunction) = {
    (cC(conj, true) :: (conj.negatedConjs.map(cC(_, false)).toList)).filter(_._1.length == 1)
  }

  def conjToClause(conj : Conjunction, negated : Boolean) : List[Literal] = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, conj.negatedConjs.length == 0 || conj.negatedConjs.length == 1)
    //-END-ASSERTION-//////////////////////////////////////////////////////////
    val predLiterals = predToLiteral(conj.predConj, negated)
    val negLiterals = conj.negatedConjs.toList.map(conjToClause(_, !negated)).flatten
    predLiterals ++ negLiterals
  }

  def clauseWidth(conj : Conjunction) = conjToClause(conj, false).length

  // Finds last open branch
  def incTable(table : Table, inputClauses : List[Conjunction]) = {
    // Find last closed branch (i.e., last closed)
    val incIdx = table indexOf (table.find(_._2.isEmpty).get)
    val (branch, closingPair, step) = table(incIdx)
    val incBranch = (branch, closingPair, step + 1)
    val newStep = step + 1
    val maxStep = branch.length + (inputClauses.map(clauseWidth(_)).sum)
    if (newStep >= maxStep) {
      None
    } else {
      val newTable = ((for (i <- 0 until incIdx) yield table(i)) ++ (incBranch :: (for (i <- (incIdx + 1) until table.length) yield table(i)).toList)).toList
      println("+++++++++++++++")
      println("incTable")
      for (b <- table)
        println("\t" + b)
      println("---------")
      for (b <- newTable)
        println("\t" + b)
      println("+++++++++++++++")
      Some(newTable)
    }
  }

  def extractConstants(conjs : List[Conjunction]) : BREUOrder = {
    (for (c <- conjs) yield c.constants).toSet.flatten.toList.map((_, false))
  }

  def solve(closedFor : Conjunction, termOrder : TermOrder) = {
    // Since the formula is in CNF, everything should be in the negated conjunctions
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ConnectionProver.AC, closedFor.predConj.size == 0 && closedFor.arithConj.isEmpty)
    //-END-ASSERTION-//////////////////////////////////////////////////////////

    println("\n\nSolving Table")
    val clauses = closedFor.negate.iterator.toList.reverse
    println("Input Clauses: ")
    for (c <- clauses)
      println("\t" + c + " => " + conjToClause(c, false))

    val baseOrder = extractConstants(clauses) ++ List((new ConstantTerm("MIN"), false))
    println("Base Order: " + baseOrder)

    var maxDepth = 10
    var maxWidth = 10

    def tryFirstClause(idx : Int) = {

      val (firstClause, terms, newOrder) = fullInst(clauses(idx), "base")

      println("\n\nTrying with inital clause: " + firstClause)

      val initTable  =
        for ((form, ass) <- conjToClause(firstClause, false)) yield {
          ((form :: ass), None, 0) : Branch
        }

      // We have to extract all terms in the problem
      val initOrder = (terms ++ baseOrder)

      val result = solveTable(initTable, initOrder, clauses, maxDepth, maxWidth, 0)
      if (result.isEmpty) {
        println("Could not close table")
        None
      } else {
        val (finalTable, finalOrder) = result.get
        // println("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
        // println("Final Order: " + finalOrder)
        // println("---------------------------")
        // println("Final Table:")
        // for (b <- finalTable)
        //   println("\t" + b)
        Some(finalTable, finalOrder)
      }
    }


    var table = None : Option[(Table, BREUOrder)]
    var tryIdx = 0
    while (table.isEmpty && tryIdx < clauses.length) {
      table = tryFirstClause(tryIdx)
      tryIdx += 1
    }

    if (!table.isEmpty) {
      val (finalTable, finalOrder) = table.get
      val (unifiable, finalMap) = unifyBranches(finalTable, finalOrder)
      println("CLOSED TABLE:")
      for (b <- finalTable)
        println("\t" + b)
      println("Using: " + finalMap)
    } else {
      println("Could not close table")
    }

    Goal(List(closedFor), Set(), Vocabulary(termOrder), preSettings)
  }
}
