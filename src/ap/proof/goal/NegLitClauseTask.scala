/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.terfor.conjunctions.{Conjunction, NegatedConjunctions,
                               Quantifier, ReduceWithConjunction,
                               IterativeClauseMatcher}
import ap.terfor.preds.PredConj
import ap.util.{Debug, Logic, Seqs}
import ap.proof.tree.{ProofTree, ProofTreeFactory}

object NegLitClauseTask {
  
  private val AC = Debug.AC_COMPLEX_FORMULAS_TASK

  /**
   * Return <code>true</code> if <code>f</code> is a formula that can be handled
   * by this task
   */
  def isCoveredFormula(f : Conjunction) : Boolean =
    !f.quans.isEmpty &&
    (f.quans forall (Quantifier.EX ==)) &&
    ((IterativeClauseMatcher isMatchable f) != IterativeClauseMatcher.Matchable.No)
    // TODO: find a proper condition when nested quantifiers can be allowed here
   // f.negatedConjs.isEmpty

}

class NegLitClauseTask(_formula : Conjunction, _age : Int)
                       extends FormulaTask(_formula, _age) {

  val priority : Int = -10000 + age

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(NegLitClauseTask.AC, !formula.isTrue)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
  
  /**
   * Perform the actual task (whatever needs to be done with <code>formula</code>)
   */
  def apply(goal : Goal, ptf : ProofTreeFactory) : ProofTree = {
    val order = goal.order
    val voc = goal.vocabulary
    
    val eager = 
      (IterativeClauseMatcher isMatchable formula) match {
        case IterativeClauseMatcher.Matchable.Complete => true
        case IterativeClauseMatcher.Matchable.ProducesLits => false
      }
    
    val oldMatcher = goal.compoundFormulas.quantifierClauses(eager)
    val newClauses =
      NegatedConjunctions(oldMatcher.clauses.elements ++ Iterator.single(formula),
                          order)
    
    val collector = goal.getInferenceCollector
    val (instances, newMatcher) =
      oldMatcher.updateClauses(newClauses,
                               goal.mayAlias,
                               goal.reduceWithFacts,
                               (voc.constantFreedom.isShielded(_, voc.bindingContext)),
                               collector, order)
    
    val newCF = goal.compoundFormulas.updateQuantifierClauses(eager, newMatcher)
    val newTasks = for (f <- instances; t <- goal.formulaTasks(f)) yield t
    
    ptf.updateGoal(newCF, newTasks, collector.getCollection, goal)
  }

  /**
   * Create a new <code>FormulaTask</code> by updating the value of
   * <code>formula</code>
   */
  protected def updateFormula(f : Conjunction, goal : Goal) : FormulaTask =
    new NegLitClauseTask(f, age)

  /**
   * Return <code>true</code> if <code>f</code> is a formula that can be handled
   * by this task
   */
  def isCoveredFormula(f : Conjunction) : Boolean =
    NegLitClauseTask isCoveredFormula f

  val name : String = "NegLitClause"

}
