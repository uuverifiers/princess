/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

package ap.proof.goal;

import scala.collection.mutable.ArrayBuilder

import ap.proof._
import ap.terfor.{Term, Formula, TermOrder, ConstantTerm, VariableTerm}
import ap.terfor.conjunctions.{Conjunction, Quantifier, ReduceWithConjunction,
                               NegatedConjunctions}
import ap.terfor.linearcombination.LinearCombination
import ap.basetypes.IdealInt
import ap.terfor.arithconj.ArithConj
import ap.terfor.equations.{ColumnSolver, NegEquationConj, EquationConj}
import ap.terfor.substitutions.{Substitution, ConstantSubst, PseudoConstantSubst,
                                ComposeSubsts}
import ap.terfor.preds.{Atom, PredConj}
import ap.util.{Logic, Debug, Seqs}
import ap.proof.tree.{ProofTree, ProofTreeFactory}
import ap.proof.certificates.BranchInferenceCollector

case object FactsNormalisationTask extends EagerTask {

  val AC = Debug.AC_FACTS_TASK
  
  def apply(goal : Goal, ptf : ProofTreeFactory) : ProofTree = {
    
    val collector = goal.getInferenceCollector
    
    var facts = goal.facts
    var eliminatedConstants = goal.eliminatedConstants
    var postProcessor : ProofTree => ProofTree = ((p) => p)
    var order = goal.order
    var bindingContext = goal.bindingContext
    var constantFreedom = goal.constantFreedom
    var definedSyms = goal.definedSyms
    var iteration = 0
    
    ////////////////////////////////////////////////////////////////////////////
    // normalise facts

    def positiveEqsSolvable : Boolean =
      facts.arithConj.positiveEqs exists (!_.leadingCoeff.isOne)
    
    def solvePositiveEqs : Unit = {
      val solver = new GoalColumnSolver (facts.arithConj.positiveEqs, eliminatedConstants,
                                         "sc_" + goal.age + "_" + iteration,
                                         order, bindingContext, constantFreedom,
                                         definedSyms, ptf, collector)
      val (newEqConj, newOrder) = solver.result
  
      order = newOrder
      bindingContext = solver.bindingContext
      constantFreedom = solver.constantFreedom
      facts = facts.updatePositiveEqs(newEqConj)(order)
      eliminatedConstants = solver.eliminatedConstants
      definedSyms = solver.definedSyms
      postProcessor = postProcessor compose solver.postProcessor      
    }

    if (positiveEqsSolvable) solvePositiveEqs

    var cont : Boolean = true
    while (cont) {
      // propagate the solved equations into the other facts
      facts = ReduceWithConjunction(Conjunction.TRUE, order)(facts, collector)

      if (facts.isFalse) {
        // then the goal can be closed immediately. if a proof is being
        // recorded, the latest vocabulary has to be written back to
        // the goal (otherwise, the proof might contain dangling symbols)
        return if (collector.isLogging)
          postProcessor(ptf.updateGoal(Conjunction.FALSE,
                                       Vocabulary(order, bindingContext, constantFreedom),
                                       collector.getCollection, goal))
        else
          ptf.updateGoal(Conjunction.FALSE, goal)
      }
        
      iteration = iteration + 1
      // if the equations have changed, we might have to solve them again
      if (positiveEqsSolvable)
        solvePositiveEqs
      else
        cont = false
    }

    val updatedVocabulary = Vocabulary(order, bindingContext, constantFreedom)
      
    ////////////////////////////////////////////////////////////////////////////
    // update clauses

    val reducer = ReduceWithConjunction(facts, order)

    def illegalQFClause(c : Conjunction) =
      c.isTrue || c.isLiteral || c.isNegatedConjunction ||
      (!Seqs.disjoint(c.constants, eliminatedConstants) ||
       !Conjunction.collectQuantifiers(c).isEmpty) &&
      !constantFreedom.isShielded(c, bindingContext)

    val (newTasks, newCompoundFormulas) =
      if (collector.isLogging) {
        // if we are producing proofs, we mostly check for subsumed clauses
        // that can be removed

        def qfClauseMapping(conjs : NegatedConjunctions)
                           : (Seq[Conjunction], Seq[Conjunction]) = {
          val otherStuff, realClauses = ArrayBuilder.make[Conjunction]

          for (c <- conjs) {
            val reducedC = reducer(c)
            if (!reducedC.isFalse)
              (if (reducedC.isTrue || reducedC.isLiteral || illegalQFClause(c))
                 otherStuff
               else
                 realClauses) += c
          }
          
          (otherStuff.result, realClauses.result)
        }

        goal.compoundFormulas.mapQFClauses(
          qfClauseMapping _,
          Goal.formulaTasks(_, goal.age, eliminatedConstants,
                            updatedVocabulary, goal.settings),
          order)
      } else {
        val reducerObj : Conjunction => Conjunction = reducer.apply _
        goal.compoundFormulas.mapQFClauses(
          (c:NegatedConjunctions) => reducer(c) partition (illegalQFClause _),
          Goal.formulaTasks(_, goal.age, eliminatedConstants,
                            updatedVocabulary, goal.settings),
          order)
      }

    ////////////////////////////////////////////////////////////////////////////
    // create a new goal

    if (newTasks.isEmpty &&
        facts == goal.facts &&
        newCompoundFormulas == goal.compoundFormulas) {
      // nothing has changed and the application of this task was unnecessary
      ptf.updateGoal(goal)
    } else {
      val allNewTasks =
        if (facts.predConj == goal.facts.predConj)
          newTasks
        else
          newTasks ++ (LazyMatchTask addTask goal)
      
      postProcessor(ptf.updateGoal(facts, newCompoundFormulas,
                                   eliminatedConstants, updatedVocabulary,
                                   definedSyms sortBy order,
                                   allNewTasks, collector.getCollection, goal))
    }
  }

}


////////////////////////////////////////////////////////////////////////////////

private class GoalColumnSolver(eqs : EquationConj,
                               var eliminatedConstants : Set[ConstantTerm],
                               constBasename : String,
                               order : TermOrder, 
                               var bindingContext : BindingContext,
                               var constantFreedom : ConstantFreedom,
                               var definedSyms : Substitution,
                               ptf : ProofTreeFactory,
                               logger : BranchInferenceCollector)
              extends ColumnSolver(eqs, logger, order) {
  
  private var constCounter : Int = 0
  
  /**
   * The function that is supposed to be applied to the resulting proof tree
   * (adding the <code>QuantifiedTree</code>, <code>SubstTree</code>
   * constructors)
   */
  var postProcessor : ProofTree => ProofTree = ((p) => p)
  
  //////////////////////////////////////////////////////////////////////////////
  
  protected def isSolvableEq(lc : LinearCombination, order : TermOrder) =
    if (lc.leadingCoeff.isOne) {
      None
    } else if (noneOrTwoElimConstants(lc)) {
      // normal column operation
      Some(reduceWithLeadingCoeff(lc, order))
    } else {
      // then lc contains exactly one eliminated constant, which is the leading
      // term and has a coefficient that is not 1
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(FactsNormalisationTask.AC,
                      !lc.leadingCoeff.isOne && isEliminated(lc.leadingTerm)
                      &&
                      Logic.forall(1, lc.size, (i) => !isEliminated(lc getTerm i)))
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      Some(makeLeadingTermSmall(lc, order))
    }

  private def newConst : ConstantTerm = {
    val res = new ConstantTerm(constBasename + "_" + constCounter)
    constCounter = constCounter + 1
    res
  }
  
  private def addDefinedSym(subst : Substitution, order : TermOrder) =
    definedSyms = ComposeSubsts(definedSyms sortBy order, subst, order)
  
  /**
   * Introduce a small constant as new name for the leading term of
   * <code>lc</code> (rule div-close)
   */
  private def makeLeadingTermSmall(lc : LinearCombination, order : TermOrder)
                                      : (Term, LinearCombination, TermOrder) = {
    assert(!logger.isLogging) // TODO

    val leadingCoeff = lc.leadingCoeff
    val leadingTerm = lc.leadingTerm
    
    val smallConst = newConst
    val extendedOrder = order.extend(smallConst, lc.constants)
    
    // the new constant (times the old leading coefficient) has to be
    // substituted in the closing constraint
    val symDefinition = LinearCombination(leadingTerm, order)
    val substLC = LinearCombination.sum(leadingCoeff, symDefinition,
                                        IdealInt.MINUS_ONE, lc, order)
    val backSubst = new PseudoConstantSubst(leadingCoeff, smallConst,
                                            substLC, extendedOrder)
    
    // the negated divisibility judgement has to be added disjunctively
    // to the closing constraint
    val var0 = LinearCombination(VariableTerm(0), order)
    val lcMod = LinearCombination.sum(leadingCoeff, var0,
                                      -leadingCoeff, symDefinition,
                                      IdealInt.ONE, lc,
                                      order)
    val notDividedByLC = Conjunction.quantify(Array(Quantifier.ALL),
                                              NegEquationConj(lcMod, order),
                                              order)
                                            
    val oldVocabulary = Vocabulary(order, bindingContext, constantFreedom)
    postProcessor = postProcessor compose
            ((p:ProofTree) => ptf.weaken(p, definedSyms(notDividedByLC), oldVocabulary))
    addDefinedSym(backSubst, extendedOrder)
    
    (smallConst, symDefinition, extendedOrder)
  }
  
  /**
   * Introduce a new small constant and reduce the coefficients of
   * <code>lc</code> with the leading coefficient (rules col-red, col-red-subst)
   */
  private def reduceWithLeadingCoeff(lc : LinearCombination,
                                     order : TermOrder)
                                      : (Term, LinearCombination, TermOrder) = {
    val symDefinition = lc.reduceWithLeadingCoeff
    val smallConst = newConst
    
    if (isEliminated(lc.leadingTerm)) {
      // then also the new constant can be eliminated, and has to be put in
      // between the non-eliminated and the eliminated constants
      val extendedOrder = order.extend(smallConst,
                                       eliminatedConstants & lc.constants)

      logger.columnReduce(lc.leadingTerm.asInstanceOf[ConstantTerm], smallConst,
                          symDefinition, false, extendedOrder)
    
      eliminatedConstants = eliminatedConstants + smallConst
      val oldVocabulary = Vocabulary(order, bindingContext, constantFreedom)
      bindingContext = bindingContext.addAndContract(smallConst, Quantifier.ALL)
      constantFreedom = constantFreedom addTopStatus List(smallConst)
      postProcessor = postProcessor compose
                      ((p:ProofTree) =>
                       ptf.quantify(p, Quantifier.ALL, List(smallConst),
                                    oldVocabulary, extendedOrder))
      (smallConst, symDefinition, extendedOrder)
    } else {
      // then it is not possible to eliminate the new constant, and the constant
      // can be made smaller than all other symbols
      val extendedOrder = order.extend(smallConst, lc.constants)

      logger.columnReduce(lc.leadingTerm.asInstanceOf[ConstantTerm], smallConst,
                          symDefinition, true, extendedOrder)
      
      val backSubst = ConstantSubst(smallConst, symDefinition, extendedOrder)
      addDefinedSym(backSubst, extendedOrder)
      (smallConst, symDefinition, extendedOrder)
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  
  private def isEliminated(t : Term) : Boolean = t match {
    case t : ConstantTerm => eliminatedConstants contains t
    case _ => false
  }

  /**
   * Determine whether the linear combination <code>lc</code> contains either
   * none or at least two terms that are eliminated in <code>goal</code>
   */
  private def noneOrTwoElimConstants(lc : LinearCombination) : Boolean = {
    def post(b : Boolean) = {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPost(FactsNormalisationTask.AC,
                       b ==
                       (Logic.exists(0, lc.size, (i) =>
                        Logic.exists(i+1, lc.size, (j) =>
                          isEliminated(lc getTerm i) && isEliminated(lc getTerm j))))
                        ||
                        (lc.termIterator forall (!isEliminated(_))))
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      b
    }

    post (if (lc.isEmpty) {
            true
          } else if (isEliminated(lc.leadingTerm)) {
            (lc.size >= 2) && isEliminated(lc getTerm 1)
          } else {
            true
          })
  }
}
