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

import ap.terfor.{Formula, TermOrder, ComputationLogger}
import ap.terfor.conjunctions.{Conjunction, Quantifier}
import ap.terfor.preds.{Atom, PredConj, Predicate}
import ap.terfor.inequalities.InEqConj
import ap.util.{Debug, Seqs, Logic}
import ap.proof.tree.{ProofTree, ProofTreeFactory}
import ap.parameters.Param

object AddFactsTask {
  
  private val AC = Debug.AC_COMPLEX_FORMULAS_TASK

  /**
   * Return <code>true</code> if <code>f</code> is a formula that can be handled
   * by this task
   */
  def isCoveredFormula(f : Conjunction) : Boolean =
    !f.isFalse &&
    (f.isTrue || f.isLiteral ||
     (f.isNegatedConjunction && f.negatedConjs(0).negatedConjs.isEmpty)) && 
    f.quans.isEmpty

}

class AddFactsTask(_formula : Conjunction, _age : Int)
      extends FormulaTask(_formula, _age) {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(AddFactsTask.AC, !formula.isFalse)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  val priority : Int = age - 20000
  
  /**
   * Perform the actual task (whatever needs to be done with <code>formula</code>)
   */
  def apply(goal : Goal, ptf : ProofTreeFactory) : ProofTree =
    if (formula.isTrue) {
      // then the goal can be closed immediately
      ptf.updateGoal(Conjunction.FALSE, goal)
    } else if (formula.isLiteral) {
      addFacts(Conjunction.negate(formula, goal.order), goal, ptf)
    } else {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(AddFactsTask.AC, formula.isNegatedConjunction)
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      val disj = formula.negatedConjs(0)
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      // possibly existing quantifiers should have been pulled out and
      // should not occur at this point
      Debug.assertInt(AddFactsTask.AC,
                      disj.quans.isEmpty && disj.negatedConjs.isEmpty)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
            
      // the literals of the negated conjunction can be added as facts to
      // the goal
      addFacts(disj, goal, ptf)
    }

  private def addFacts(newFacts : Conjunction,
                       goal : Goal,
                       ptf : ProofTreeFactory) : ProofTree = {
    val order = goal.order
    val (updatedFacts, updatedInferences) = {
      val collector = goal.getInferenceCollector
      val allFacts =
        if (Param.PROOF_CONSTRUCTION(goal.settings))
          // when constructing proofs, we decompose conjunctions of inequalities
          // so that all computations concerning the new inequalities can be
          // recorded
          Array(goal.facts, newFacts.updateInEqs(InEqConj.TRUE)(order)).elements ++
            (for (lc <- newFacts.arithConj.inEqs.elements) yield InEqConj(lc, order))
        else
          Array(goal.facts, newFacts).elements
      val updatedFacts = Conjunction(List(), allFacts, collector, order)
      (updatedFacts, collector.getCollection)
    }
    val newTasks =
      if (newFacts.predConj.isTrue) List() else (LazyMatchTask addTask goal)
    ptf.updateGoal(updatedFacts, newTasks, updatedInferences, goal)
  }
  
  /**
   * Create a new <code>FormulaTask</code> by updating the value of
   * <code>formula</code>
   */
  protected def updateFormula(f : Conjunction, goal : Goal) : FormulaTask =
    new AddFactsTask(f, age)

  /**
   * Return <code>true</code> if <code>f</code> is a formula that can be handled
   * by this task
   */
  protected[goal] def isCoveredFormula(f : Conjunction) : Boolean =
    AddFactsTask.isCoveredFormula(f)

  val name : String = "AddFacts"

}
